/**
 * Differential comparison of the reference kernel (src/engine.ts) with the clean-room
 * oracle of the evaluation program Π(Σ) (test/oracle/pi-sigma.ts, spec/core.md §5 item 14).
 *
 * Each seeded state uses the boundaries B, B1 ⊑ B and B2 ⊑ B (plus ⊤_B) in a random topology
 * (a diamond with B12 ⊑ B1, B2, an ambiguous diamond with a second maximal common sub-boundary
 * B12b, siblings of unknown overlap, or declared disjoint siblings),
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
 * Where a meet the program needs is ambiguous, both must report an error (core.md §5 item 14,
 * Role); where no rule needs it, both must evaluate. When every handle the items name belongs to a
 * domain, the kernel must also be query-conservative (item 14).
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
  collectHandles,
  equiv,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  substituteHandle,
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
  readonly ambiguous: boolean;
};

function handleSpec(id: string): HandleSpec {
  return { id, criterion: `I(${id})`, kind: "structural" };
}

/** The handles an item names outside the quantifiers that bind them. */
function freeHandles(item: Item, bound: ReadonlySet<string>, out: Set<string>): void {
  switch (item.kind) {
    case "atom":
      for (const r of item.roles) {
        if (!bound.has(r.handle)) {
          out.add(r.handle);
        }
      }
      return;
    case "equiv":
      for (const h of [item.left, item.right]) {
        if (!bound.has(h)) {
          out.add(h);
        }
      }
      return;
    case "flip":
      freeHandles(item.inner, bound, out);
      return;
    case "and":
    case "or":
      freeHandles(item.left, bound, out);
      freeHandles(item.right, bound, out);
      return;
    case "implies":
      freeHandles(item.antecedent, bound, out);
      freeHandles(item.consequent, bound, out);
      return;
    case "forall":
    case "exists": {
      const inner = new Set(bound).add(item.variable);
      freeHandles(item.body, inner, out);
      if (item.domainConstraint !== undefined) {
        freeHandles(item.domainConstraint, inner, out);
      }
      return;
    }
    default:
      return;
  }
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
  const topology = rng.pick(["diamond", "ambiguous-diamond", "unknown-siblings", "disjoint-siblings"] as const);
  const names: string[] = ["B", "B1", "B2"];
  if (topology === "diamond" || topology === "ambiguous-diamond") {
    bs.defineBoundary("B12", { parents: ["B1", "B2"], handles: domB12.map(handleSpec) });
    names.push("B12");
  }
  if (topology === "ambiguous-diamond") {
    // A second maximal common sub-boundary makes B1 ⊓ B2 ambiguous (core.md §2 item 4).
    bs.defineBoundary("B12b", { parents: ["B1", "B2"], handles: domB12.map(handleSpec) });
    names.push("B12b");
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
        if (rng.bool(0.5)) {
          bs.defineMeet("X", cell, `X${cell}`);
        }
      }
    }
    if (names.includes("D1") && rng.bool(0.4) && bs.meetStatus("X", "D1").kind === "unknown") {
      bs.declareDisjoint("X", "D1");
    }
  }

  // Half of the ambiguous states track no implication, so no rule needs the ambiguous meet.
  const implicationFree = topology === "ambiguous-diamond" && rng.bool(0.5);

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
    // ⊤_B ranges over every declared handle (audit-top-domain-quantifiers).
    const domain = rng.bool(0.15) ? TOP_BOUNDARY : boundary();
    const body =
      !implicationFree && depth > 0 && rng.bool(0.3)
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
        return implicationFree
          ? baseAtom()
          : implies(compound(depth - 1), rng.bool(0.15) ? bottom() : compound(depth - 1));
      default:
        return baseAtom();
    }
  };

  const observed: { readonly id: string; readonly observation: PiObservation }[] = [];
  let next = 0;
  // Observations are many-sorted (core.md §2 item 6): a handle outside Dom(b) is replaced by a
  // handle of Dom(b), or, when Dom(b) is empty, the item by a nullary atom. Dom(⊤_B) is the union
  // of the declared domains.
  const sorted = (b: string, item: Item): Item => {
    const domain = bs.handlesOf(b).map((h) => h.id);
    let out = item;
    for (const h of collectHandles(item)) {
      if (!domain.includes(h)) {
        if (domain.length === 0) {
          return atom(rng.pick(NULLARY));
        }
        out = substituteHandle(out, h, rng.pick(domain));
      }
    }
    return out;
  };
  const observe = (b: string, polarity: Polarity, raw: Item): void => {
    next += 1;
    const id = `w${next}`;
    const item = sorted(b, raw);
    if (polarity === "+") {
      engine.observePositive(b, item, id);
    } else {
      engine.observeNegative(b, item, id);
    }
    observed.push({ id, observation: { boundary: b, polarity, item } });
  };

  const observationCount = rng.int(2, 7);
  for (let i = 0; i < observationCount; i++) {
    const item = !implicationFree && rng.bool(profile.conditional)
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
  if (!implicationFree && rng.bool(0.2)) {
    const c = { boundary: boundary(), item: baseAtom() };
    collapses.push({ ...c, id: engine.addStructuralCollapse(c.boundary, c.item) });
  }

  const closures: { readonly domain: string; readonly id: string }[] = [];
  for (const d of [...names, TOP_BOUNDARY]) {
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
    ambiguous: topology === "ambiguous-diamond",
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
  allValidCoverStates: number;
  ambiguousErrors: number;
  ambiguousEvaluated: number;
  queryConservative: number;
};

/** Assert kernel/oracle agreement on one state and accumulate what it exercised. */
function compareState(state: RandomState, ctx: string, coverage: Coverage): void {
  // An ambiguous meet the program needs is an error in both; one that nothing needs is in neither.
  const attempt = <T>(run: () => T): { readonly value?: T; readonly error?: string } => {
    try {
      return { value: run() };
    } catch (error) {
      return { error: error instanceof Error ? error.message : String(error) };
    }
  };
  const kernel = attempt(() => state.engine.evaluate(state.queries));
  const oracle = attempt(() =>
    evaluatePi({
      boundaries: state.boundaries,
      observations: state.observations,
      incompatibilities: state.incompatibilities,
      collapses: state.collapses,
      closedDomains: state.closedDomains,
      queries: state.queries,
      historyItems: state.historyItems,
    }),
  );
  if (kernel.error !== undefined || oracle.error !== undefined) {
    assert.ok(
      kernel.error !== undefined && oracle.error !== undefined,
      `${ctx} kernel and oracle both report an error or neither does (kernel: ${kernel.error ?? "none"}; oracle: ${oracle.error ?? "none"})`,
    );
    assert.match(kernel.error, /ambiguous/i, `${ctx} kernel error is an ambiguous meet`);
    assert.match(oracle.error, /ambiguous/i, `${ctx} oracle error is an ambiguous meet`);
    coverage.ambiguousErrors += 1;
    coverage.states += 1;
    return;
  }
  const snap = kernel.value as ReturnType<InquiryEngine["evaluate"]>;
  const model = oracle.value as ReturnType<typeof evaluatePi>;

  // Query conservativity (core.md §5 item 14): when every handle the items name belongs to a domain
  // of 𝔅(Σ), the queried items add slots and change neither the local status nor the authority of
  // any slot of U(Σ, ∅), nor No-Gluts.
  const named = new Set<string>();
  const items = [
    ...state.observations.map((o) => o.item),
    ...state.incompatibilities.flatMap((c) => [c.left, c.right]),
    ...state.collapses.map((c) => c.item),
    ...state.historyItems,
    ...state.queries,
  ];
  for (const it of items) {
    freeHandles(it, new Set(), named);
  }
  const domains = new Set(state.boundaries.nonEmptyBoundaries().flatMap((b) => state.boundaries.handlesOf(b).map((h) => h.id)));
  if ([...named].every((h) => domains.has(h))) {
    const plain = state.engine.evaluate();
    for (const item of plain.universe()) {
      for (const b of model.boundaries) {
        const where = `${ctx} query conservativity at (${b}, ${itemKey(item)})`;
        assert.equal(snap.localStatus(b, item), plain.localStatus(b, item), `${where} local status`);
        for (const p of ["+", "-"] as const) {
          assert.equal(snap.authorityOf(b, p, item), plain.authorityOf(b, p, item), `${where} authority ${p}`);
        }
      }
    }
    assert.equal(snap.isCollisionFree(), plain.isCollisionFree(), `${ctx} query conservativity of No-Gluts`);
    coverage.queryConservative += 1;
  }
  if (state.ambiguous) {
    coverage.ambiguousEvaluated += 1;
  }

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
  // With every registered cover valid, every witnessed cover is valid (item 5): registered meets are
  // greatest lower bounds, and disjoint boundaries share no non-empty sub-boundary (item 4).
  if (state.boundaries.registeredCovers().length > 0 && snap.coverObligations().length === 0) {
    for (const b of model.boundaries) {
      for (const cells of state.boundaries.witnessedCoversOf(b)) {
        assert.equal(
          state.boundaries.judgeCover(b, cells).kind,
          "valid",
          `${ctx} {${cells.join(", ")}} ▷ ${b} derived from valid registered covers is valid`,
        );
      }
    }
    coverage.allValidCoverStates += 1;
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
    allValidCoverStates: 0,
    ambiguousErrors: 0,
    ambiguousEvaluated: 0,
    queryConservative: 0,
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
    assert.ok(coverage.allValidCoverStates > 0, "[suite=general] some state has only valid registered covers");
    assert.ok(coverage.ambiguousEvaluated > 0, "[suite=general] some state with an ambiguous meet evaluates");
    assert.ok(coverage.ambiguousErrors > 0, "[suite=general] some state needs an ambiguous meet");
    assert.ok(coverage.queryConservative > 0, "[suite=general] some state is checked for query conservativity");
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
