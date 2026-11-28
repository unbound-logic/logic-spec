// The plan of a kernel mutation run (.github/workflows/mutation.yml). It lists every mutant with
// Stryker's own instrumenter, keeps those of the run's scope, sizes the number of shards from the
// time the tests take without a mutant as a shard runs them, deals the mutants to the shards in
// pieces that keep each shard's count near the mean, and checks, by instrumenting each shard's
// share as the shard will, that every mutant of the scope lies in exactly one shard. Rules:
// `mutation-triage-and-sharding` in docs/design-review.md.
//
//   node scripts/mutation/plan.mjs --scope full|diff|list [--base REF] [--mutate PATTERNS]
//        --seconds N --concurrency N --out DIR [--shards N]
//
// --scope full takes every mutant; diff, the mutants that span a line of src/ changed between
// --base (by default the latest v* tag reachable from HEAD) and HEAD; list, the mutants that
// --mutate's Stryker patterns select (a file, or file:startLine[:startColumn]-endLine[:endColumn]).
// --concurrency is the number of mutants a shard runs at once, and --seconds the time the test
// command took without a mutant when run that many times at once, which is what a mutant no test
// catches costs in a shard; --shards overrides the count the time gives. It writes plan.json, one
// shard-K.json and shard-K.mutate a shard, and summary.md into DIR, and prints the workflow's
// outputs.

import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { parseArgs } from "node:util";
import {
  MAX_SHARDS,
  PIECE_LIMIT,
  SHARD_IGNORE_REASON,
  SHARD_MINUTES,
  changedLines,
  countProblems,
  dealPieces,
  directiveProblems,
  inDiff,
  instrument,
  mutantKey,
  mutatedFiles,
  parsePatterns,
  pieces,
  readConfig,
  share,
  shardIgnorer,
  shareRanges,
  within,
} from "./lib.mjs";

const { values: args } = parseArgs({
  options: {
    scope: { type: "string" },
    base: { type: "string", default: "" },
    mutate: { type: "string", default: "" },
    seconds: { type: "string" },
    concurrency: { type: "string" },
    out: { type: "string" },
    shards: { type: "string", default: "" },
  },
});

const fail = (message) => {
  console.error(`::error::${message}`);
  process.exit(1);
};
const wholeNumber = (text, name) => {
  if (!/^[1-9][0-9]*$/.test(text ?? "")) fail(`${name} is no whole number above 0: '${text}'`);
  return Number(text);
};

const root = process.cwd();
const git = (...a) => execFileSync("git", a, { cwd: root, encoding: "utf8", maxBuffer: 64 * 1024 * 1024 });

const scope = args.scope;
if (!["full", "diff", "list"].includes(scope)) fail(`the scope is none of full, diff and list: '${scope}'`);
const seconds = wholeNumber(args.seconds, "--seconds");
const concurrency = wholeNumber(args.concurrency, "--concurrency");
if (!args.out) fail("--out names no directory");
const forced = args.shards === "" ? undefined : wholeNumber(args.shards, "--shards");

// The rules, before anything is listed: no exclusion in the configuration, and each disable comment
// names one mutator and gives its reason.
let config;
try {
  config = readConfig(root);
} catch (error) {
  fail(error.message);
}
const files = mutatedFiles(root);
const badDirectives = directiveProblems(root, files);
if (badDirectives.length > 0) {
  for (const p of badDirectives) console.error(p);
  fail(`${badDirectives.length} Stryker comment(s) do not read "// Stryker disable next-line <Mutator>: <reason>"`);
}

// Every mutant, as `stryker run` lists it over the whole of src/.
const all = await instrument(root, config, new Map(files.map((f) => [f, true])));
const active = all.filter((m) => m.status !== "Ignored");
const ignored = all.filter((m) => m.status === "Ignored");

// The run's scope.
let inScope;
let described;
let base = "";
let baseSha = "";
if (scope === "full") {
  inScope = () => true;
  described = "every mutant of src/";
} else if (scope === "diff") {
  base = args.base.trim();
  if (base === "") {
    try {
      base = git("describe", "--tags", "--abbrev=0", "--match", "v*", "HEAD").trim();
    } catch {
      fail("no v* tag is reachable from HEAD; give --base");
    }
  }
  if (!/^[A-Za-z0-9._/-]+$/.test(base) || base.startsWith("-")) fail(`the base is no ref this plan reads: '${base}'`);
  try {
    baseSha = git("rev-parse", "--verify", `${base}^{commit}`).trim();
  } catch {
    fail(`the base names no commit: '${base}' (a shallow checkout lacks it; fetch the history and tags)`);
  }
  const diff = git("-c", "core.quotePath=false", "diff", "--no-ext-diff", "--no-textconv", "--text", "--no-renames", "-U0", `${baseSha}...HEAD`, "--", "src");
  const lines = changedLines(diff);
  inScope = (m) => inDiff(lines, m);
  described = `the mutants that span a line of src/ changed since ${base} (${baseSha.slice(0, 7)})`;
} else {
  if (args.mutate.trim() === "") fail("the list scope needs --mutate");
  let patterns;
  try {
    patterns = parsePatterns(args.mutate, files);
  } catch (error) {
    fail(error.message);
  }
  inScope = (m) => {
    const p = patterns.get(m.file);
    return p === true || (Array.isArray(p) && p.some((l) => within(m, l)));
  };
  described = `the mutants within ${[...patterns].map(([f, p]) => (p === true ? f : `${f} (${p.length} range(s))`)).join(", ")}`;
}

const planned = active.filter(inScope);
const plannedIgnored = ignored.filter(inScope);

// The shards the baseline's time needs: each mutant is taken to run every test, as one that no test
// catches does, `concurrency` at once, each taking the time the tests took so.
const needed = planned.length === 0 ? 0 : Math.ceil((planned.length * seconds) / (concurrency * SHARD_MINUTES * 60));
const wanted = planned.length === 0 ? 0 : Math.min(MAX_SHARDS, Math.max(1, forced ?? needed));

// The pieces, dealt in source order to the shards.
const list = wanted > 0 ? pieces(active, inScope, PIECE_LIMIT) : [];
const shards = wanted > 0 ? dealPieces(list, Math.min(wanted, list.length)) : [];
const shares = shards.map((s, k) => share(k, s));

// Every planned mutant in exactly one shard, as the pieces say, and as each shard's own run of the
// instrumenter, with its ranges and its ignorer, lists it.
const problems = countProblems(
  planned.map(mutantKey),
  shards.flatMap((s) => s.pieces.flatMap((p) => p.mutants.map(mutantKey))),
);
const ignoredKeys = new Set(ignored.map(mutantKey));
for (const [k, s] of shares.entries()) {
  const ranges = new Map();
  for (const l of shareRanges(s)) ranges.set(l.file, [...(ranges.get(l.file) ?? []), l]);
  const listed = await instrument(root, config, ranges, [shardIgnorer(root, s)]);
  const run = listed.filter((m) => m.status !== "Ignored").map(mutantKey);
  for (const p of countProblems(shards[k].pieces.flatMap((p) => p.mutants.map(mutantKey)), run)) problems.push(`shard ${k}: ${p}`);
  for (const m of listed) {
    if (m.status === "Ignored" && m.reason !== SHARD_IGNORE_REASON && !ignoredKeys.has(mutantKey(m))) {
      problems.push(`shard ${k}: ${mutantKey(m)} is ignored by a comment in the shard and not in the listing`);
    }
  }
}
if (problems.length > 0) {
  for (const p of problems.slice(0, 50)) console.error(p);
  fail(`the shards do not hold the scope's mutants, each once (${problems.length} problem(s))`);
}

// The plan, as the shards and the report read it.
const out = args.out;
fs.mkdirSync(out, { recursive: true });
for (const name of fs.readdirSync(out)) fail(`${out} is not empty: ${name}`);
const strip = (m) => ({ file: m.file, sl: m.sl, sc: m.sc, el: m.el, ec: m.ec, mutator: m.mutator, replacement: m.replacement });
const shardOf = new Map();
shards.forEach((s, k) => s.pieces.forEach((p) => p.mutants.forEach((m) => shardOf.set(mutantKey(m), k))));
const plan = {
  scope,
  described,
  base,
  baseSha,
  head: git("rev-parse", "HEAD").trim(),
  seconds,
  concurrency,
  shardMinutes: SHARD_MINUTES,
  needed,
  shards: shards.length,
  pieceLimit: PIECE_LIMIT,
  mutants: planned.map((m) => ({ ...strip(m), shard: shardOf.get(mutantKey(m)) })),
  ignored: plannedIgnored.map((m) => ({ ...strip(m), reason: m.reason })),
};
fs.writeFileSync(path.join(out, "plan.json"), `${JSON.stringify(plan, null, 1)}\n`);
for (const s of shares) {
  fs.writeFileSync(path.join(out, `shard-${s.shard}.json`), `${JSON.stringify(s, null, 1)}\n`);
  fs.writeFileSync(path.join(out, `shard-${s.shard}.mutate`), s.mutate.join(","));
}

const sizes = shards.map((s) => s.size);
const trees = list.filter((p) => p.kind === "tree");
const summary = [
  "## Mutation plan",
  "",
  `Scope: ${scope}, ${described}.`,
  "",
  `- Mutants: ${planned.length} to run, ${plannedIgnored.length} ignored by a comment with its reason.`,
  `- Tests without a mutant, ${concurrency} at once as a shard runs them: ${seconds} s.`,
  planned.length === 0
    ? "- Shards: none, since the scope holds no mutant."
    : `- Shards: ${shards.length} (the time needs ${needed} of ${SHARD_MINUTES} minutes at most, if no test caught any mutant; at most ${MAX_SHARDS}${forced ? `; ${forced} asked for` : ""}).`,
  planned.length === 0
    ? ""
    : `- Mutants a shard: ${Math.min(...sizes)} to ${Math.max(...sizes)}, dealt in source order in ${list.length} pieces: ${list.length - trees.length} of at most ${PIECE_LIMIT} mutants within one node, and ${trees.length} holding the own mutants of nodes too large to deal whole (${trees.reduce((n, p) => n + p.mutants.length, 0)} mutant(s)).`,
  "",
].join("\n");
fs.writeFileSync(path.join(out, "summary.md"), summary);
console.error(summary);

const reason = planned.length === 0 ? "no-mutants" : "sharded";
console.log([`reason=${reason}`, `count=${shards.length}`, `mutants=${planned.length}`, `shards=${JSON.stringify(shards.map((_, k) => k))}`].join("\n"));
