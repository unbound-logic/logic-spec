/**
 * Differential comparison of the reference kernel (src/engine.ts) with the clean-room
 * oracle of the evaluation program Π(Σ) (test/oracle/pi-sigma.ts, spec/core.md §5 item 14).
 *
 * Each seeded state uses the boundaries B, B1 ⊑ B and B2 ⊑ B (plus ⊤_B) in a random topology
 * (a diamond with B12 ⊑ B1, B2, siblings of unknown overlap, or declared disjoint siblings),
 * sometimes with an unrelated C, a sub-boundary X ⊑ B whose overlap with B1 and B2 is declared
 * disjoint, settled by a registered common sub-boundary, or left unknown, and a nested D1 ⊑ B1.
 * States carry monotone random handle sets, positive and negative observations (some later
 * retracted), conditionals, incompatibilities, congruences, structural collapses, covers that
 * the topology may leave valid, unverified or invalid (core.md §2 item 5), domain closures, and
 * a Withdraw of some constraint (item 7), with queries built from atoms, `∧`, `∨`, `~`, `→` and
 * quantifiers over closed and unclosed domains. For every state the kernel and the oracle must
 * agree on U(Σ, Q); for every slot of 𝔅(Σ) × U(Σ, Q) (the queried slots included) on the local
 * status, the authority of each polarity, obstruction and the revision obligations; on the
 * OverlapUnknown and cover obligations; and on the ⊆-minimal witnessed covers of every boundary.
 * Recorded theorems and reflection values are not generated, since the oracle omits those two
 * rows (AMBIGUITIES.md A15).
 *
 * Item 14 tracks ⊥ and every item named by a past transition, retracted observations and
 * withdrawn constraints included. The kernel keeps those items itself; the oracle receives them
 * through PiState.historyItems (AMBIGUITIES.md A23, A38) and tracks ⊥ on its own (A22), so both
 * are compared on the same universe. A withdrawn cover leaves the shared boundary system, which
 * both read.
 *
 * UL_FUZZ_MULTIPLIER scales the number of states; UL_FUZZ_SEED replays a single state.
 */

import assert from "node:assert/strict";
import { test } from "node:test";
import { BoundarySystem, TOP_BOUNDARY, type HandleSpec } from "../src/boundary.ts";
import { InquiryEngine } from "../src/engine.ts";
import {
  and,
  atom,
  bottom,
  equiv,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  type Item,
  type Polarity,
} from "../src/syntax.ts";
import {
  evaluatePi,
  type PiCollapse,
  type PiIncompatibility,
  type PiObservation,
} from "./oracle/pi-sigma.ts";

class Rng {
  #state: number;

  constructor(seed: number) {
    this.#state = seed >>> 0;
  }

  next(): number {
    this.#state = (this.#state + 0x6d2b79f5) >>> 0;
    let t = Math.imul(this.#state ^ (this.#state >>> 15), 1 | this.#state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  int(min: number, max: number): number {
    return min + Math.floor(this.next() * (max - min + 1));
  }

  bool(p = 0.5): boolean {
    return this.next() < p;
  }

  pick<T>(items: readonly T[]): T {
    const picked = items[this.int(0, items.length - 1)];
    if (picked === undefined) {
      throw new Error("Rng.pick called on an empty array.");
    }
    return picked;
  }

  subset<T>(items: readonly T[], p: number): T[] {
    return items.filter(() => this.bool(p));
  }
}

/** Seeds for one suite; a single UL_FUZZ_SEED replaces them, UL_FUZZ_MULTIPLIER scales them. */
function suiteSeeds(suiteId: number, defaultCount: number): { readonly seeds: number[]; readonly replay: boolean } {
  const seedEnv = process.env.UL_FUZZ_SEED;
  if (seedEnv !== undefined && seedEnv.trim() !== "") {
    const parsed = Number.parseInt(seedEnv.trim(), 10);
    if (!Number.isNaN(parsed)) {
      return { seeds: [parsed >>> 0], replay: true };
    }
  }
  let mult = 1;
  const multEnv = process.env.UL_FUZZ_MULTIPLIER;
  if (multEnv !== undefined && multEnv.trim() !== "") {
    const parsed = Number.parseFloat(multEnv.trim());
    if (Number.isFinite(parsed) && parsed > 0) {
      mult = parsed;
    }
  }
  const count = Math.max(1, Math.round(defaultCount * mult));
  const seeds: number[] = [];
  for (let i = 0; i < count; i++) {
    seeds.push((Math.imul(suiteId + 101, 0x9e3779b1) ^ Math.imul(i + 1, 0x85ebca6b)) >>> 0);
  }
  return { seeds, replay: false };
}

const HANDLES = ["a", "b", "c"] as const;
const NULLARY = ["X0", "X1", "X2", "X3"] as const;

type Profile = {
  /** Probability that an observation is a conditional. */
  readonly conditional: number;
  /** Number of incompatibilities. */
  readonly incompatibilities: readonly [number, number];
  /** Probability that a domain is closed. */
  readonly closure: number;
  /** Probability that a query is a quantifier. */
  readonly quantifier: number;
  /** Probability of a domain sweep: one polarity observed for every handle of a domain. */
  readonly sweep: number;
  /** Probability that a state retracts one or two of its observations. */
  readonly retraction: number;
  /** Probability that a state withdraws one of its constraints. */
  readonly withdrawal: number;
};

const GENERAL: Profile = { conditional: 0.3, incompatibilities: [0, 2], closure: 0.4, quantifier: 0.3, sweep: 0.2, retraction: 0.4, withdrawal: 0.35 };
const CONFLICTS: Profile = { conditional: 0.5, incompatibilities: [1, 3], closure: 0.3, quantifier: 0.15, sweep: 0.1, retraction: 0.4, withdrawal: 0.25 };
const QUANTIFIERS: Profile = { conditional: 0.2, incompatibilities: [0, 1], closure: 0.6, quantifier: 0.7, sweep: 0.6, retraction: 0.3, withdrawal: 0.35 };

type RandomState = {
  readonly boundaries: BoundarySystem;
  readonly engine: InquiryEngine;
  readonly observations: PiObservation[];
  readonly incompatibilities: PiIncompatibility[];
  readonly collapses: PiCollapse[];
  readonly closedDomains: string[];
  readonly queries: Item[];
  /** Items of past transitions no longer in force: retracted observations, withdrawn constraints. */
  readonly historyItems: Item[];
  /** The kind of the constraint withdrawn, if any. */
  readonly withdrawn: string | undefined;
};

function handleSpec(id: string): HandleSpec {
  return { id, criterion: `I(${id})`, kind: "structural" };
}

/** Build a random state through the kernel's inquiry transitions, recording it for the oracle. */
function randomState(rng: Rng, profile: Profile): RandomState {
  const bs = new BoundarySystem();
  const domB = rng.subset(HANDLES, 0.75);
  const domB1 = rng.subset(domB, 0.7);
  const domB2 = rng.subset(domB, 0.7);
  const domB12 = rng.subset(
    domB1.filter((h) => domB2.includes(h)),
    0.7,
  );
  bs.defineBoundary("B", { nativeRelations: ["P", "Q", "R"], handles: domB.map(handleSpec) });
  bs.defineBoundary("B1", { parents: ["B"], handles: domB1.map(handleSpec) });
  bs.defineBoundary("B2", { parents: ["B"], handles: domB2.map(handleSpec) });
  // Random topology (core.md §2 item 4): the diamond with a registered common sub-boundary B12,
  // siblings B1 and B2 whose overlap is unknown, or siblings declared disjoint; and sometimes an
  // unrelated top-level boundary C, whose overlap with the B family is unknown.
  const topology = rng.pick(["diamond", "unknown-siblings", "disjoint-siblings"] as const);
  const names: string[] = ["B", "B1", "B2"];
  if (topology === "diamond") {
    bs.defineBoundary("B12", { parents: ["B1", "B2"], handles: domB12.map(handleSpec) });
    names.push("B12");
  } else if (topology === "disjoint-siblings") {
    bs.declareDisjoint("B1", "B2");
  }
  if (rng.bool(0.5)) {
    bs.defineBoundary("C", { nativeRelations: ["P", "Q", "R"], handles: rng.subset(HANDLES, 0.7).map(handleSpec) });
    names.push("C");
  }
  // Cover stress (item 5): a nested cell D1 ⊑ B1, and a sub-boundary X ⊑ B whose overlap with each
  // of B1, B2 (and D1) is declared disjoint, settled by a registered common sub-boundary, or left
  // unknown, so that covers of B and B1 come out valid, unverified or invalid.
  if (rng.bool(0.35)) {
    bs.defineBoundary("D1", { parents: ["B1"], handles: rng.subset(domB1, 0.7).map(handleSpec) });
    names.push("D1");
  }
  if (rng.bool(0.5)) {
    const domX = rng.subset(domB, 0.7);
    bs.defineBoundary("X", { parents: ["B"], handles: domX.map(handleSpec) });
    names.push("X");
    for (const cell of ["B1", "B2"] as const) {
      const r = rng.next();
      if (r < 0.4) {
        bs.declareDisjoint("X", cell);
      } else if (r < 0.65) {
        bs.defineBoundary(`X${cell}`, { parents: ["X", cell] });
        names.push(`X${cell}`);
      }
    }
    if (names.includes("D1") && rng.bool(0.4) && bs.meetStatus("X", "D1").kind === "unknown") {
      bs.declareDisjoint("X", "D1");
    }
  }

  const engine = new InquiryEngine(bs);
  const coverIds: string[] = [];
  if (rng.bool(0.45)) {
    coverIds.push(engine.witnessCover("B", ["B1", "B2"]));
  }
  if (names.includes("B12") && rng.bool(0.2)) {
    coverIds.push(engine.witnessCover("B1", ["B12"]));
  }
  if (names.includes("D1") && rng.bool(0.5)) {
    coverIds.push(engine.witnessCover("B1", ["D1"]));
  }

  const handle = (): string => rng.pick(HANDLES);
  const boundary = (): string => rng.pick(names);
  const unary = (relation: "P" | "Q", h: string): Item => atom(relation, [{ role: "arg", handle: h }]);
  const baseAtom = (): Item => {
    const k = rng.int(0, 9);
    if (k < 4) {
      return atom(rng.pick(NULLARY));
    }
    if (k < 8) {
      return unary(rng.pick(["P", "Q"] as const), handle());
    }
    if (k < 9) {
      return atom("R", [
        { role: "from", handle: handle() },
        { role: "to", handle: handle() },
      ]);
    }
    return equiv(rng.pick(["B", "B1"] as const), handle(), handle());
  };
  const quantifier = (depth: number): Item => {
    const domain = boundary();
    const body =
      depth > 0 && rng.bool(0.3)
        ? implies(unary("P", "x"), unary("Q", "x"))
        : rng.bool(0.25)
          ? flip(unary(rng.pick(["P", "Q"] as const), "x"))
          : unary(rng.pick(["P", "Q"] as const), "x");
    const constraint = rng.bool(0.35) ? (rng.bool(0.5) ? unary("Q", "x") : flip(unary("Q", "x"))) : undefined;
    return rng.bool(0.5) ? forall("x", domain, body, constraint) : exists("x", domain, body, constraint);
  };
  const compound = (depth: number): Item => {
    if (depth <= 0) {
      return baseAtom();
    }
    if (rng.bool(profile.quantifier * 0.5)) {
      return quantifier(depth);
    }
    switch (rng.int(0, 5)) {
      case 0:
        return flip(compound(depth - 1));
      case 1:
        return and(compound(depth - 1), compound(depth - 1));
      case 2:
        return or(compound(depth - 1), compound(depth - 1));
      case 3:
        return implies(compound(depth - 1), rng.bool(0.15) ? bottom() : compound(depth - 1));
      default:
        return baseAtom();
    }
  };

  const observed: { readonly id: string; readonly observation: PiObservation }[] = [];
  let next = 0;
  const observe = (b: string, polarity: Polarity, item: Item): void => {
    next += 1;
    const id = `w${next}`;
    if (polarity === "+") {
      engine.observePositive(b, item, id);
    } else {
      engine.observeNegative(b, item, id);
    }
    observed.push({ id, observation: { boundary: b, polarity, item } });
  };

  const observationCount = rng.int(2, 7);
  for (let i = 0; i < observationCount; i++) {
    const item = rng.bool(profile.conditional)
      ? implies(baseAtom(), rng.bool(0.1) ? bottom() : baseAtom())
      : rng.bool(0.2)
        ? compound(1)
        : baseAtom();
    const polarity: Polarity = item.kind === "bottom" ? "-" : rng.bool(0.6) ? "+" : "-";
    observe(rng.bool(0.1) ? TOP_BOUNDARY : boundary(), polarity, item);
  }
  if (rng.bool(0.25)) {
    observe(rng.pick(["B", "B1"] as const), "+", equiv("B", handle(), handle()));
  }
  // Domain sweep: enumerative quantifier rules see every handle covered, and an opposite record
  // planted on some boundary can leave a swept record present but not Live.
  if (rng.bool(profile.sweep)) {
    const domain = boundary();
    const relation = rng.pick(["P", "Q"] as const);
    const polarity: Polarity = rng.bool(0.5) ? "+" : "-";
    const at = rng.bool(0.5) ? domain : "B";
    const swept = bs.handlesOf(domain).map((h) => h.id);
    for (const h of swept) {
      observe(at, polarity, unary(relation, h));
    }
    if (swept.length > 0 && rng.bool(0.5)) {
      observe(boundary(), polarity === "+" ? "-" : "+", unary(relation, rng.pick(swept)));
    }
  }

  // Retract: the record goes, the item stays tracked (item 14).
  const historyItems: Item[] = [];
  const retractCount = rng.bool(profile.retraction) ? rng.int(1, 2) : 0;
  for (let i = 0; i < retractCount && observed.length > 0; i++) {
    const [gone] = observed.splice(rng.int(0, observed.length - 1), 1);
    if (gone !== undefined) {
      assert.equal(engine.retract(gone.id), true);
      historyItems.push(gone.observation.item);
    }
  }
  const observations = observed.map((o) => o.observation);

  const incompatibilities: (PiIncompatibility & { readonly id: string })[] = [];
  const incompatibilityCount = rng.int(profile.incompatibilities[0], profile.incompatibilities[1]);
  for (let i = 0; i < incompatibilityCount; i++) {
    const c = { boundary: boundary(), left: baseAtom(), right: baseAtom() };
    incompatibilities.push({ ...c, id: engine.addIncompatibility(c.boundary, c.left, c.right) });
  }

  const collapses: (PiCollapse & { readonly id: string })[] = [];
  if (rng.bool(0.2)) {
    const c = { boundary: boundary(), item: baseAtom() };
    collapses.push({ ...c, id: engine.addStructuralCollapse(c.boundary, c.item) });
  }

  const closures: { readonly domain: string; readonly id: string }[] = [];
  for (const d of names) {
    if (rng.bool(profile.closure)) {
      closures.push({ domain: d, id: engine.closeDomain(d) });
    }
  }

  // Withdraw (item 7): the constraint leaves C_B, and the items it named stay tracked (item 14).
  // A withdrawn cover leaves the shared boundary system, which the oracle reads as well.
  let withdrawn: string | undefined;
  const candidates = [
    ...incompatibilities.map((c) => ({ kind: "incompatibility", id: c.id })),
    ...collapses.map((c) => ({ kind: "collapse", id: c.id })),
    ...closures.map((c) => ({ kind: "closure", id: c.id })),
    ...coverIds.map((id) => ({ kind: "cover", id })),
  ];
  if (candidates.length > 0 && rng.bool(profile.withdrawal)) {
    const gone = rng.pick(candidates);
    assert.equal(engine.withdraw(gone.id), true);
    withdrawn = gone.kind;
    const inc = incompatibilities.findIndex((c) => c.id === gone.id);
    if (inc >= 0) {
      const [c] = incompatibilities.splice(inc, 1);
      if (c !== undefined) {
        historyItems.push(c.left, c.right);
      }
    }
    const col = collapses.findIndex((c) => c.id === gone.id);
    if (col >= 0) {
      const [c] = collapses.splice(col, 1);
      if (c !== undefined) {
        historyItems.push(c.item, implies(c.item, bottom()));
      }
    }
    const clo = closures.findIndex((c) => c.id === gone.id);
    if (clo >= 0) {
      closures.splice(clo, 1);
    }
  }
  const closedDomains = closures.map((c) => c.domain);

  const queries: Item[] = [];
  const queryCount = rng.int(2, 6);
  for (let i = 0; i < queryCount; i++) {
    queries.push(rng.bool(profile.quantifier) ? quantifier(1) : compound(rng.int(1, 2)));
  }

  return {
    boundaries: bs,
    engine,
    observations,
    incompatibilities,
    collapses,
    closedDomains,
    queries,
    historyItems,
    withdrawn,
  };
}

type Coverage = {
  states: number;
  retractions: number;
  undetermined: number;
  quarantined: number;
  collisions: number;
  closedUniversalGrounded: number;
  closedExistentialExcluded: number;
  overlapObligations: number;
  invalidCovers: number;
  unverifiedCovers: number;
  withdrawals: number;
};

/** Assert kernel/oracle agreement on one state and accumulate what it exercised. */
function compareState(state: RandomState, ctx: string, coverage: Coverage): void {
  const snap = state.engine.evaluate(state.queries);
  const model = evaluatePi({
    boundaries: state.boundaries,
    observations: state.observations,
    incompatibilities: state.incompatibilities,
    collapses: state.collapses,
    closedDomains: state.closedDomains,
    queries: state.queries,
    historyItems: state.historyItems,
  });

  // A retracted observation supplies no record but keeps its item in U(Σ, Q).
  const kernelKeys = new Set(snap.universe().map(itemKey));
  for (const item of state.historyItems) {
    assert.ok(kernelKeys.has(itemKey(item)), `${ctx} retracted item ${itemKey(item)} stays tracked`);
  }
  if (state.historyItems.length > 0) {
    coverage.retractions += 1;
  }

  const kernelUniverse = snap.universe().map(itemKey).sort();
  const oracleUniverse = model.universe.map(itemKey).sort();
  assert.deepEqual(kernelUniverse, oracleUniverse, `${ctx} U(Σ, Q)`);

  const queried = new Set(state.queries.map(itemKey));
  for (const row of model.rows) {
    const label = `${ctx} (${row.boundary}, ${itemKey(row.item)})${queried.has(itemKey(row.item)) ? " [queried]" : ""}`;
    assert.equal(snap.localStatus(row.boundary, row.item), row.localStatus, `${label} local status`);
    for (const p of ["+", "-"] as const) {
      const authority = snap.authorityOf(row.boundary, p, row.item);
      assert.equal(authority, row.authority[p], `${label} authority ${p}`);
      assert.equal(snap.isLive(row.boundary, p, row.item), row.authority[p] === "Live", `${label} isLive ${p}`);
      if (authority === "Undetermined") {
        coverage.undetermined += 1;
      } else if (authority === "Quarantined") {
        coverage.quarantined += 1;
      }
    }
    assert.equal(snap.isObstructed(row.boundary, row.item), row.obs !== "false", `${label} obstruction`);
    if (row.localStatus === "Collision") {
      coverage.collisions += 1;
    }
    const closed =
      (row.item.kind === "forall" || row.item.kind === "exists") &&
      state.closedDomains.includes(row.item.domain);
    if (closed && row.item.kind === "forall" && row.localStatus === "Grounded") {
      coverage.closedUniversalGrounded += 1;
    }
    if (closed && row.item.kind === "exists" && row.localStatus === "Excluded") {
      coverage.closedExistentialExcluded += 1;
    }
  }

  const kernelRev = snap
    .revisionObligations()
    .map((r) => `${r.boundary} ${r.itemKey}`)
    .sort();
  const oracleRev = model.revisionObligations.map((r) => `${r.boundary} ${itemKey(r.item)}`).sort();
  assert.deepEqual(kernelRev, oracleRev, `${ctx} revision obligations`);

  // OverlapUnknown (item 14): opposite present records across an unknown overlap, each unordered
  // pair once.
  const pairKey = (a: string, b: string, k: string): string => `${[a, b].sort().join(" ")} ${k}`;
  const kernelOverlap = snap
    .overlapObligations()
    .map((o) => pairKey(o.left, o.right, o.itemKey))
    .sort();
  const oracleOverlap = model.overlapObligations.map((o) => pairKey(o.left, o.right, itemKey(o.item))).sort();
  assert.deepEqual(kernelOverlap, oracleOverlap, `${ctx} OverlapUnknown obligations`);
  coverage.overlapObligations += kernelOverlap.length;

  // Cover obligations (item 5): each invalid or unverified registered cover, with the
  // sub-boundaries that refute it or leave it unsettled.
  const kernelCover = snap
    .coverObligations()
    .map((o) => `${o.coverId} ${o.validity} ${[...o.witnesses].sort().join(",")}`)
    .sort();
  const oracleCover = model.coverObligations
    .map((o) => `${o.id} ${o.validity} ${[...o.subBoundaries].sort().join(",")}`)
    .sort();
  assert.deepEqual(kernelCover, oracleCover, `${ctx} cover obligations`);
  for (const o of snap.coverObligations()) {
    if (o.validity === "invalid") {
      coverage.invalidCovers += 1;
    } else {
      coverage.unverifiedCovers += 1;
    }
  }

  // Witnessed covers (item 5): the ⊆-minimal covers of each boundary, which give every cover rule
  // instance of Π(Σ); the oracle lists only those (AMBIGUITIES.md A36).
  const signature = (cells: readonly string[]): string => [...cells].sort().join(",");
  for (const b of model.boundaries) {
    const all = state.boundaries.witnessedCoversOf(b).map((cells) => [...new Set(cells)]);
    const minimal = all.filter(
      (cells) => !all.some((other) => other.length < cells.length && other.every((c) => cells.includes(c))),
    );
    const kernelCovers = [...new Set(minimal.map(signature))].sort();
    const oracleCovers = model.witnessedCovers
      .filter((w) => w.boundary === b)
      .map((w) => signature(w.cells))
      .sort();
    assert.deepEqual(kernelCovers, oracleCovers, `${ctx} minimal witnessed covers of ${b}`);
  }
  if (state.withdrawn !== undefined) {
    coverage.withdrawals += 1;
  }
  coverage.states += 1;
}

function runSuite(suiteId: number, name: string, defaultCount: number, profile: Profile): Coverage {
  const coverage: Coverage = {
    states: 0,
    retractions: 0,
    undetermined: 0,
    quarantined: 0,
    collisions: 0,
    closedUniversalGrounded: 0,
    closedExistentialExcluded: 0,
    overlapObligations: 0,
    invalidCovers: 0,
    unverifiedCovers: 0,
    withdrawals: 0,
  };
  const { seeds, replay } = suiteSeeds(suiteId, defaultCount);
  for (const seed of seeds) {
    const ctx = `[suite=${name} seed=${seed}]`;
    compareState(randomState(new Rng(seed), profile), ctx, coverage);
  }
  if (!replay) {
    assert.equal(coverage.states, seeds.length, `[suite=${name}] every state compared`);
  }
  return coverage;
}

function test_differential_general_states(): void {
  const coverage = runSuite(1, "general", 120, GENERAL);
  if (coverage.states > 1) {
    assert.ok(coverage.collisions > 0, "[suite=general] some state reaches Collision");
    assert.ok(coverage.quarantined > 0, "[suite=general] some record is Quarantined");
    assert.ok(coverage.retractions > 0, "[suite=general] some state retracts an observation");
    assert.ok(coverage.overlapObligations > 0, "[suite=general] some state records OverlapUnknown");
    assert.ok(coverage.invalidCovers > 0, "[suite=general] some registered cover is invalid");
    assert.ok(coverage.unverifiedCovers > 0, "[suite=general] some registered cover is unverified");
    assert.ok(coverage.withdrawals > 0, "[suite=general] some state withdraws a constraint");
  }
}

function test_differential_conflict_heavy_states(): void {
  const coverage = runSuite(2, "conflicts", 100, CONFLICTS);
  if (coverage.states > 1) {
    assert.ok(coverage.undetermined > 0, "[suite=conflicts] some authority is Undetermined");
    assert.ok(coverage.collisions > 0, "[suite=conflicts] some state reaches Collision");
    assert.ok(coverage.retractions > 0, "[suite=conflicts] some state retracts an observation");
  }
}

function test_differential_quantifiers_over_closed_and_unclosed_domains(): void {
  const coverage = runSuite(3, "quantifiers", 100, QUANTIFIERS);
  if (coverage.states > 1) {
    assert.ok(coverage.closedUniversalGrounded > 0, "[suite=quantifiers] some closed ∀ is Grounded");
    assert.ok(coverage.closedExistentialExcluded > 0, "[suite=quantifiers] some closed ∃ is Excluded");
  }
}

test("differential: general random states", test_differential_general_states);
test("differential: conflict-heavy random states", test_differential_conflict_heavy_states);
test(
  "differential: quantifiers over closed and unclosed domains",
  test_differential_quantifiers_over_closed_and_unclosed_domains,
);
