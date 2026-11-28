// Shared parts of the kernel mutation pipeline (.github/workflows/mutation.yml): the identity of a
// Stryker mutant across a listing and a report, the listing itself, the plan's shards, and the
// ignorer that keeps each shard to its share. The report needs none of Stryker's packages, so this
// module imports them only when a listing is asked for. Rules: `mutation-triage-and-sharding` in
// docs/design-review.md.

import fs from "node:fs";
import path from "node:path";

/** The reason the shard ignorer gives a mutant that the plan dealt to another shard. */
export const SHARD_IGNORE_REASON = "mutation-shard: dealt to another shard";
/** The ignorer's name, as stryker.config.json lists it. */
export const SHARD_IGNORER = "mutation-shard";
/** The environment variable that names a shard's share for the ignorer. */
export const SHARD_FILE_ENV = "MUTATION_SHARD_FILE";
/** The most shards a run takes: GitHub's free plan runs 20 jobs at once, and other runs may need some. */
export const MAX_SHARDS = 16;
/** The time the plan gives one shard's mutants, in minutes. */
export const SHARD_MINUTES = 30;
/**
 * The most mutants a piece dealt whole may hold. Small pieces dealt in source order spread every
 * region of the kernel over the shards: the mutants of some functions cost far more than others,
 * and run 46172125302 dealt evaluatePi's 1,180 mutants whole to one shard, which ran longest.
 * Pieces of 16 keep the nodes too large to deal whole to about 200 mutants of the full run.
 */
export const PIECE_LIMIT = 16;
/** The files Stryker mutates, as stryker.config.json must list them. */
export const MUTATE_PATTERNS = ["src/**/*.ts"];
/** Stryker 10's mutator names, which a disable comment may name. */
export const MUTATOR_NAMES = [
  "ArithmeticOperator",
  "ArrayDeclaration",
  "ArrowFunction",
  "AssignmentOperator",
  "BlockStatement",
  "BooleanLiteral",
  "CallExpression",
  "ConditionalExpression",
  "EqualityOperator",
  "LogicalOperator",
  "MethodExpression",
  "ObjectLiteral",
  "OptionalChaining",
  "Regex",
  "StringLiteral",
  "UnaryOperator",
  "UpdateOperator",
];

// ---------------------------------------------------------------------------------- locations

// A location is { file, sl, sc, el, ec }: lines from 1 and columns from 0, as Babel's node.loc and
// Stryker's --mutate ranges read them. Stryker's API counts lines from 0; its JSON report counts
// columns from 1.

/** A path relative to `root`, with forward slashes. */
export function relative(root, file) {
  return path.relative(root, path.resolve(root, file)).split(path.sep).join("/");
}

/** The location and identity of a mutant from Stryker's instrumenter API. */
export function fromApi(root, m) {
  return {
    file: relative(root, m.fileName),
    sl: m.location.start.line + 1,
    sc: m.location.start.column,
    el: m.location.end.line + 1,
    ec: m.location.end.column,
    mutator: m.mutatorName,
    replacement: m.replacement,
    status: m.status,
    reason: m.statusReason,
  };
}

/** The location and identity of a mutant from Stryker's JSON report. */
export function fromReport(file, m) {
  return {
    file,
    sl: m.location.start.line,
    sc: m.location.start.column - 1,
    el: m.location.end.line,
    ec: m.location.end.column - 1,
    mutator: m.mutatorName,
    replacement: m.replacement,
    status: m.status,
    reason: m.statusReason,
  };
}

/** A location as a --mutate range, and as the key of its group. */
export const locKey = (l) => `${l.file}:${l.sl}:${l.sc}-${l.el}:${l.ec}`;
/** A mutant's identity: its location, mutator and replacement. */
export const mutantKey = (m) => `${locKey(m)} ${m.mutator} ${JSON.stringify(m.replacement)}`;

const notAfter = (al, ac, bl, bc) => al < bl || (al === bl && ac <= bc);
/** Whether location `inner` lies within `outer`, as Stryker decides it for a --mutate range. */
export function within(inner, outer) {
  return notAfter(outer.sl, outer.sc, inner.sl, inner.sc) && notAfter(inner.el, inner.ec, outer.el, outer.ec);
}
/** Whether two locations share any position. */
export function overlaps(a, b) {
  return notAfter(a.sl, a.sc, b.el, b.ec) && notAfter(b.sl, b.sc, a.el, a.ec);
}

// ----------------------------------------------------------------------------- configuration

/** stryker.config.json, checked against the rules: no exclusion, no global ignore. */
export function readConfig(root) {
  const config = JSON.parse(fs.readFileSync(path.join(root, "stryker.config.json"), "utf8"));
  const problems = [];
  if (JSON.stringify(config.mutate) !== JSON.stringify(MUTATE_PATTERNS)) problems.push(`mutate must be ${JSON.stringify(MUTATE_PATTERNS)}`);
  if ((config.mutator?.excludedMutations ?? []).length > 0) problems.push("mutator.excludedMutations must be empty");
  if (JSON.stringify(config.ignorers ?? []) !== JSON.stringify([SHARD_IGNORER])) problems.push(`ignorers must be ["${SHARD_IGNORER}"] alone`);
  if (config.ignoreStatic) problems.push("ignoreStatic must be off");
  if (problems.length > 0) throw new Error(`stryker.config.json breaks the mutation rules: ${problems.join("; ")}`);
  return config;
}

/** The files Stryker mutates: every .ts file under src/, relative to `root`, sorted. */
export function mutatedFiles(root) {
  const out = [];
  const walk = (dir) => {
    for (const entry of fs.readdirSync(path.join(root, dir), { withFileTypes: true })) {
      const rel = `${dir}/${entry.name}`;
      if (entry.isDirectory()) walk(rel);
      else if (entry.isFile() && entry.name.endsWith(".ts")) out.push(rel);
    }
  };
  walk("src");
  return out.sort();
}

/**
 * Every Stryker comment directive in the mutated files that breaks the rule: a directive must read
 * `// Stryker disable next-line <Mutator>: <reason>`, name one mutator, and give a reason. One
 * message a directive.
 */
export function directiveProblems(root, files) {
  const strict = new RegExp(`^\\s*// Stryker disable next-line (${MUTATOR_NAMES.join("|")}): \\S.*$`);
  const problems = [];
  for (const file of files) {
    const lines = fs.readFileSync(path.join(root, file), "utf8").split(/\r?\n/);
    lines.forEach((line, i) => {
      if (/Stryker\s+(disable|restore)/i.test(line) && !strict.test(line)) problems.push(`${file}:${i + 1}: ${line.trim()}`);
    });
  }
  return problems;
}

// ---------------------------------------------------------------------------------- listing

const silent = () => {};
const logger = {
  trace: silent,
  debug: silent,
  info: silent,
  warn: silent,
  error: silent,
  fatal: silent,
  isTraceEnabled: () => false,
  isDebugEnabled: () => false,
  isInfoEnabled: () => false,
  isWarnEnabled: () => false,
  isErrorEnabled: () => false,
  isFatalEnabled: () => false,
};

/**
 * The mutants Stryker's own instrumenter makes, as `stryker run` would: `files` maps each file to
 * mutate to `true` or to its ranges (locations), and `ignorers` are Stryker ignorer objects. Each
 * mutant comes back with `status` "Ignored" and its `reason` when a directive or an ignorer
 * ignored it.
 */
export async function instrument(root, config, files, ignorers = []) {
  const { Instrumenter } = await import("@stryker-mutator/instrumenter");
  const input = [...files].map(([file, mutate]) => ({
    name: path.resolve(root, file),
    content: fs.readFileSync(path.join(root, file), "utf8"),
    // Stryker's own form of a range: lines from 0, columns from 0.
    mutate: mutate === true ? true : mutate.map((l) => ({ start: { line: l.sl - 1, column: l.sc }, end: { line: l.el - 1, column: l.ec } })),
  }));
  const options = { plugins: null, excludedMutations: [], ...config.mutator, ignorers };
  const result = await new Instrumenter(logger).instrument(input, options);
  return result.mutants.map((m) => fromApi(root, m));
}

// ------------------------------------------------------------------------------------ scopes

/**
 * The changed lines of each mutated file between `base` and HEAD, from `git diff -U0`. A deletion
 * marks the lines on both sides of it, so the mutants that span it are in the diff.
 */
export function changedLines(diffText) {
  const lines = new Map();
  let file;
  for (const line of diffText.split("\n")) {
    if (line.startsWith("+++ ")) {
      file = line === "+++ /dev/null" ? undefined : line.slice(4).replace(/^b\//, "");
      continue;
    }
    const hunk = /^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@/.exec(line);
    if (!hunk || file === undefined) continue;
    const start = Number(hunk[1]);
    const count = hunk[2] === undefined ? 1 : Number(hunk[2]);
    const set = lines.get(file) ?? new Set();
    if (count > 0) for (let n = start; n < start + count; n += 1) set.add(n);
    else for (const n of [start, start + 1]) if (n >= 1) set.add(n);
    lines.set(file, set);
  }
  return lines;
}

/** Whether a mutant spans a changed line. */
export function inDiff(lines, m) {
  const set = lines.get(m.file);
  if (!set) return false;
  for (let n = m.sl; n <= m.el; n += 1) if (set.has(n)) return true;
  return false;
}

/**
 * Stryker --mutate patterns, comma-separated: a file, or a file with a range
 * `startLine[:startColumn]-endLine[:endColumn]` (lines from 1, columns from 0). Returns a map from
 * each file to `true` or its ranges.
 */
export function parsePatterns(text, files) {
  const out = new Map();
  for (const raw of text.split(",").map((p) => p.trim()).filter((p) => p !== "")) {
    const m = /^(.*?):((\d+)(?::(\d+))?-(\d+)(?::(\d+))?)$/.exec(raw);
    const file = m ? m[1] : raw;
    if (!files.includes(file)) throw new Error(`the pattern ${raw} names no file Stryker mutates (${files.join(", ")})`);
    if (!m) {
      out.set(file, true);
      continue;
    }
    const loc = { file, sl: Number(m[3]), sc: Number(m[4] ?? 0), el: Number(m[5]), ec: m[6] === undefined ? Number.MAX_SAFE_INTEGER : Number(m[6]) };
    const prev = out.get(file);
    if (prev !== true) out.set(file, [...(prev ?? []), loc]);
  }
  return out;
}

// ----------------------------------------------------------------------------------- dealing

/**
 * Pieces of the run's mutants that a shard can run alone. A --mutate range selects every mutant
 * whose location lies within it, so the mutants of one syntax node cannot be split by ranges: a
 * piece is either a "unit", every mutant within one location (all in scope, at most `limit`), or
 * a "tree", the own mutants of locations too large or not wholly in scope, which a shard runs by
 * the range of the tree's root while the shard ignorer leaves out what lies within them and was
 * dealt elsewhere. `all` is every mutant not ignored by a directive; `inScope(m)` says which the
 * run takes.
 */
export function pieces(all, inScope, limit) {
  const byFile = new Map();
  for (const m of all) {
    const groups = byFile.get(m.file) ?? new Map();
    const key = locKey(m);
    const group = groups.get(key) ?? { loc: { file: m.file, sl: m.sl, sc: m.sc, el: m.el, ec: m.ec }, own: [], children: [], scope: inScope(m) };
    if (group.scope !== inScope(m)) throw new Error(`the mutants at ${key} are partly in scope`);
    group.own.push(m);
    groups.set(key, group);
    byFile.set(m.file, groups);
  }
  const out = [];
  for (const groups of byFile.values()) {
    // The containment forest of the file's locations, outer first.
    const sorted = [...groups.values()].sort((a, b) => a.loc.sl - b.loc.sl || a.loc.sc - b.loc.sc || b.loc.el - a.loc.el || b.loc.ec - a.loc.ec);
    const roots = [];
    const stack = [];
    for (const g of sorted) {
      while (stack.length > 0 && !within(g.loc, stack.at(-1).loc)) {
        if (overlaps(g.loc, stack.at(-1).loc) && !within(stack.at(-1).loc, g.loc) && !touching(g.loc, stack.at(-1).loc)) {
          throw new Error(`the locations ${locKey(g.loc)} and ${locKey(stack.at(-1).loc)} overlap without one holding the other`);
        }
        stack.pop();
      }
      (stack.length > 0 ? stack.at(-1).children : roots).push(g);
      stack.push(g);
    }
    const measure = (g) => {
      g.size = g.own.length;
      g.whole = g.scope;
      for (const c of g.children) {
        measure(c);
        g.size += c.size;
        g.whole &&= c.whole;
      }
    };
    roots.forEach(measure);
    const collect = (g, acc) => {
      acc.push(...g.own);
      g.children.forEach((c) => collect(c, acc));
      return acc;
    };
    const deal = (g, tree) => {
      if (g.scope && g.whole && g.size <= limit) {
        out.push({ kind: "unit", root: g.loc, locations: [g.loc], mutants: collect(g, []) });
        return;
      }
      let next = tree;
      if (g.scope) {
        if (!next) {
          next = { kind: "tree", root: g.loc, locations: [], mutants: [] };
          out.push(next);
        }
        next.locations.push(g.loc);
        next.mutants.push(...g.own);
      }
      g.children.forEach((c) => deal(c, next));
    };
    roots.forEach((g) => deal(g, undefined));
  }
  return out;
}

// Two locations that only meet at one position, the end of one being the start of the other.
function touching(a, b) {
  return (a.el === b.sl && a.ec === b.sc) || (b.el === a.sl && b.ec === a.sc);
}

/**
 * The run's pieces dealt to `count` shards in source order, each to the shard with the fewest
 * mutants so far: each shard's count stays within a piece of the mean, and neighbouring pieces, and
 * so each region of the kernel, go to different shards.
 */
export function dealPieces(list, count) {
  const shards = Array.from({ length: count }, () => ({ pieces: [], size: 0 }));
  const order = [...list].sort((a, b) => a.root.file.localeCompare(b.root.file) || a.root.sl - b.root.sl || a.root.sc - b.root.sc || b.root.el - a.root.el || b.root.ec - a.root.ec);
  for (const piece of order) {
    let target = shards[0];
    for (const s of shards) if (s.size < target.size) target = s;
    target.pieces.push(piece);
    target.size += piece.mutants.length;
  }
  return shards;
}

/**
 * A shard's share as the shard reads it: the --mutate ranges (each piece's root) and, for the
 * ignorer, every location the shard runs the own mutants of and every unit root.
 */
export function share(index, shard) {
  const mutate = [...new Map(shard.pieces.map((p) => [locKey(p.root), p.root])).values()];
  const keep = shard.pieces.flatMap((p) => p.locations);
  const units = shard.pieces.filter((p) => p.kind === "unit").map((p) => p.root);
  return {
    shard: index,
    mutate: mutate.map(locKey),
    keep: keep.map(locKey),
    units: units.map(locKey),
  };
}

const parseLoc = (key) => {
  const m = /^(.*):(\d+):(\d+)-(\d+):(\d+)$/.exec(key);
  if (!m) throw new Error(`no location: ${key}`);
  return { file: m[1], sl: Number(m[2]), sc: Number(m[3]), el: Number(m[4]), ec: Number(m[5]) };
};
/** A shard's --mutate ranges as locations. */
export const shareRanges = (s) => s.mutate.map(parseLoc);

/**
 * The Stryker ignorer of a shard. Within its ranges, it ignores a node, with all that lies within
 * it, when the node holds no location the shard keeps and lies within no unit of the shard: what
 * the node holds was dealt to other shards. With no share, it ignores nothing.
 */
export function shardIgnorer(root, s) {
  if (!s) return { shouldIgnore: () => undefined };
  const byFile = (keys) => {
    const map = new Map();
    for (const l of keys.map(parseLoc)) map.set(l.file, [...(map.get(l.file) ?? []), l]);
    return map;
  };
  const keep = byFile(s.keep);
  const units = byFile(s.units);
  return {
    shouldIgnore(nodePath) {
      const loc = nodePath.node?.loc;
      const name = nodePath.hub?.file?.opts?.filename;
      if (!loc || typeof name !== "string") return undefined;
      const file = relative(root, name);
      const here = { file, sl: loc.start.line, sc: loc.start.column, el: loc.end.line, ec: loc.end.column };
      if ((keep.get(file) ?? []).some((l) => within(l, here))) return undefined;
      if ((units.get(file) ?? []).some((u) => within(here, u))) return undefined;
      return SHARD_IGNORE_REASON;
    },
  };
}

// ------------------------------------------------------------------------------------- tallies

/** Counts of a list of mutants by status. */
export function tally(list) {
  const t = { Killed: 0, Timeout: 0, Survived: 0, NoCoverage: 0, Ignored: 0, CompileError: 0, RuntimeError: 0, Pending: 0 };
  for (const m of list) t[m.status] = (t[m.status] ?? 0) + 1;
  return t;
}

/** Each name counted as often as it stands: one message a name whose counts differ. */
export function countProblems(expected, actual) {
  const count = new Map();
  for (const n of expected) count.set(n, (count.get(n) ?? 0) + 1);
  for (const n of actual) count.set(n, (count.get(n) ?? 0) - 1);
  return [...count]
    .filter(([, c]) => c !== 0)
    .map(([n, c]) => (c > 0 ? `${n}: expected ${c} more time(s)` : `${n}: found ${-c} more time(s) than expected`))
    .sort();
}
