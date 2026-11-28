// The report of a kernel mutation run (.github/workflows/mutation.yml). It merges the shards'
// Stryker reports, checks that together they hold every mutant of the plan exactly once, each from
// the shard the plan dealt it to, and prints the outcomes by file. A Timeout is counted apart and
// never as caught. "Unexplained survivors" are the Survived and NoCoverage mutants: a mutant ignored
// by a disable comment carries its reason and is counted as Ignored. The score is reported, not a
// gate: survivors never fail the job; a shard that failed or a report that does not match the plan
// does. Rules: `mutation-triage-and-sharding` in docs/design-review.md.
//
//   node scripts/mutation/report.mjs --plan DIR --reports DIR --out DIR
//        [--plan-result R] [--shards-result R]
//
// --plan is the plan's directory (plan.json); --reports holds one directory a shard,
// mutation-shard-K, with Stryker's mutation.json; --out receives summary.md, survivors.txt and
// merged.json. The results are those of the workflow's plan and shard jobs.

import fs from "node:fs";
import path from "node:path";
import { parseArgs } from "node:util";
import { SHARD_IGNORE_REASON, countProblems, fromReport, mutantKey, tally } from "./lib.mjs";

const { values: args } = parseArgs({
  options: {
    plan: { type: "string" },
    reports: { type: "string" },
    out: { type: "string" },
    "plan-result": { type: "string", default: "success" },
    "shards-result": { type: "string", default: "success" },
  },
});

const problems = [];
const out = args.out;
fs.mkdirSync(out, { recursive: true });
const lines = ["## Kernel mutation report", ""];
const finish = () => {
  if (problems.length > 0) {
    lines.push("### Problems", "", ...problems.slice(0, 100).map((p) => `- ${p}`), "");
    if (problems.length > 100) lines.push(`- … and ${problems.length - 100} more`, "");
  }
  const text = `${lines.join("\n")}\n`;
  fs.writeFileSync(path.join(out, "summary.md"), text);
  console.log(text);
  if (problems.length > 0) console.error(`::error::the mutation run does not stand: ${problems.length} problem(s), listed in the summary`);
  process.exit(problems.length > 0 ? 1 : 0);
};

const planFile = path.join(args.plan ?? "", "plan.json");
if (args["plan-result"] !== "success" || !fs.existsSync(planFile)) {
  problems.push(`the plan did not succeed (${args["plan-result"]}), so no shard stands for the scope`);
  finish();
}
const plan = JSON.parse(fs.readFileSync(planFile, "utf8"));
lines.push(`Scope: ${plan.scope}, ${plan.described}. Commit ${plan.head.slice(0, 7)}.`, "");

if (plan.mutants.length === 0) {
  if (!["skipped", "success"].includes(args["shards-result"])) problems.push(`the plan made no shard, and the shards' result is ${args["shards-result"]}`);
  lines.push(`Nothing to mutate: the scope holds no mutant${plan.ignored.length > 0 ? ` (${plan.ignored.length} ignored by a comment)` : ""}.`);
  finish();
}
if (args["shards-result"] !== "success") problems.push(`the plan made ${plan.shards} shard(s), and their result is ${args["shards-result"]}`);

// Each shard's results: the mutants it ran, without those its ignorer left to other shards.
const results = [];
const sources = new Map();
const rawByKey = new Map();
const ignoredRaw = new Map();
for (let k = 0; k < plan.shards; k += 1) {
  const file = path.join(args.reports ?? "", `mutation-shard-${k}`, "mutation.json");
  if (!fs.existsSync(file)) {
    problems.push(`shard ${k} left no report`);
    continue;
  }
  const report = JSON.parse(fs.readFileSync(file, "utf8"));
  for (const [name, entry] of Object.entries(report.files ?? {})) {
    if (!sources.has(name)) sources.set(name, { language: entry.language, source: entry.source });
    for (const raw of entry.mutants) {
      const m = fromReport(name, raw);
      if (m.status === "Ignored") {
        // A mutant a disable comment ignores is ignored in every shard whose ranges hold it.
        if (m.reason !== SHARD_IGNORE_REASON && !ignoredRaw.has(mutantKey(m))) ignoredRaw.set(mutantKey(m), { ...raw, id: `${k}-${raw.id}` });
        continue;
      }
      results.push({ ...m, shard: k });
      rawByKey.set(mutantKey(m), { ...raw, id: `${k}-${raw.id}` });
    }
  }
}

// Every planned mutant once, from the shard the plan dealt it to, and nothing beside them.
const where = (list) => list.map((m) => `${mutantKey(m)} in shard ${m.shard}`);
for (const p of countProblems(where(plan.mutants), where(results))) problems.push(p);

// The outcomes of the planned mutants, by file.
const status = new Map(results.map((m) => [`${mutantKey(m)} in shard ${m.shard}`, m.status]));
const outcomes = plan.mutants.map((m) => ({ ...m, status: status.get(`${mutantKey(m)} in shard ${m.shard}`) ?? "Pending" }));
const ignored = plan.ignored.map((m) => ({ ...m, status: "Ignored" }));
const files = [...new Set([...outcomes, ...ignored].map((m) => m.file))].sort();
const percent = (n, d) => (d === 0 ? "n/a" : `${((100 * n) / d).toFixed(2)}%`);
const row = (name, list) => {
  const t = tally(list);
  const valid = t.Killed + t.Timeout + t.Survived + t.NoCoverage;
  const errors = t.CompileError + t.RuntimeError + t.Pending;
  return `| ${name} | ${percent(t.Killed + t.Timeout, valid)} | ${percent(t.Killed, valid)} | ${t.Killed} | ${t.Timeout} | ${t.Survived} | ${t.NoCoverage} | ${t.Ignored} | ${errors} | ${t.Survived + t.NoCoverage} |`;
};
lines.push(
  "| File | Stryker score | Killed only | Killed | Timeout | Survived | NoCoverage | Ignored | Errors | Unexplained |",
  "| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
  ...files.map((f) => row(f, [...outcomes, ...ignored].filter((m) => m.file === f))),
  row("**All**", [...outcomes, ...ignored]),
  "",
  "Stryker score counts Timeout as caught; Killed only does not: a mutant whose tests ran past the timeout is not shown to be caught. Unexplained is Survived plus NoCoverage: each such mutant is to be killed by a test or ignored by a disable comment that gives its reason. Errors are CompileError, RuntimeError and mutants left without an outcome.",
  "",
);
const all = tally([...outcomes, ...ignored]);
const unexplained = all.Survived + all.NoCoverage;
lines.push(`**Unexplained survivors: ${unexplained}.** Timeouts: ${all.Timeout}.`, "");

const describe = (m) => `${m.file}:${m.sl}:${m.sc + 1} ${m.mutator} → ${String(m.replacement).replace(/\s+/g, " ").slice(0, 160)}`;
const survivors = outcomes.filter((m) => m.status === "Survived" || m.status === "NoCoverage");
const timeouts = outcomes.filter((m) => m.status === "Timeout");
fs.writeFileSync(
  path.join(out, "survivors.txt"),
  [...survivors.map((m) => `${m.status}\t${describe(m)}`), ...timeouts.map((m) => `Timeout\t${describe(m)}`)].join("\n") + "\n",
);
if (plan.scope === "diff") {
  lines.push(`### Unexplained survivors in the diff since ${plan.base}`, "");
  lines.push(...(survivors.length === 0 ? ["None."] : ["```text", ...survivors.map((m) => `${m.status === "NoCoverage" ? "NoCoverage " : ""}${describe(m)}`), "```"]), "");
  lines.push("### Timeouts in the diff, not counted as caught", "");
  lines.push(...(timeouts.length === 0 ? ["None."] : ["```text", ...timeouts.map(describe), "```"]), "");
} else {
  lines.push("Each survivor and timeout is listed in survivors.txt, in the run's report artifact.", "");
}

// The shards' reports as one, which Stryker's report viewer reads.
const merged = { schemaVersion: "1.0", thresholds: { high: 80, low: 60 }, files: {} };
for (const f of files) {
  const mutants = [
    ...outcomes.filter((m) => m.file === f).map((m) => rawByKey.get(mutantKey(m))),
    ...ignored.filter((m) => m.file === f).map((m) => ignoredRaw.get(mutantKey(m))),
  ].filter(Boolean);
  merged.files[f] = { ...(sources.get(f) ?? { language: "typescript", source: "" }), mutants };
}
fs.writeFileSync(path.join(out, "merged.json"), JSON.stringify(merged));

finish();
