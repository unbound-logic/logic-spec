/**
 * Hand-computed cases for the clean-room Π(Σ) oracle in test/oracle/pi-sigma.ts
 * (spec/core.md §5 item 14, as amended in main commit 7b36043, with the three-valued meet of
 * §2 item 4 from main commit 5a385ce, and cover validity, Meet-Stability across an unknown
 * overlap and Withdraw of §2 items 5 and 7 from main commits fde28ec and a7377cf). Every
 * expectation is derived by hand from items 5 and 14 (program, rule table, Reporting section
 * under G4b, and Constraints); readings follow test/oracle/AMBIGUITIES.md.
 */

import { test } from "node:test";
import assert from "node:assert/strict";

import { BOT_BOUNDARY, BoundarySystem, TOP_BOUNDARY, type HandleSpec } from "../src/boundary.ts";
import { and, atom, bottom, equiv, exists, flip, forall, implies, itemKey, or, type Item } from "../src/syntax.ts";
import {
  evaluatePi,
  type Authority,
  type LocalStatus,
  type PiModel,
  type Truth,
} from "./oracle/pi-sigma.ts";

type Expected = {
  readonly rec?: readonly [Truth, Truth];
  readonly live?: readonly [Truth, Truth];
  readonly coll?: Truth;
  readonly obs?: Truth;
  readonly status?: LocalStatus;
  readonly authority?: readonly [Authority | null, Authority | null];
  readonly rev?: boolean;
};

function expectRow(model: PiModel, boundary: string, item: Item, expected: Expected): void {
  const row = model.at(boundary, item);
  const label = `(${boundary}, ${itemKey(item)})`;
  if (expected.rec !== undefined) {
    assert.deepEqual([row.rec["+"], row.rec["-"]], expected.rec, `${label} rec(+, -)`);
  }
  if (expected.live !== undefined) {
    assert.deepEqual([row.live["+"], row.live["-"]], expected.live, `${label} live(+, -)`);
  }
  if (expected.coll !== undefined) {
    assert.equal(row.coll, expected.coll, `${label} coll`);
  }
  if (expected.obs !== undefined) {
    assert.equal(row.obs, expected.obs, `${label} obs`);
  }
  if (expected.status !== undefined) {
    assert.equal(row.localStatus, expected.status, `${label} local status`);
  }
  if (expected.authority !== undefined) {
    assert.deepEqual(
      [row.authority["+"], row.authority["-"]],
      expected.authority,
      `${label} authority(+, -)`,
    );
  }
  if (expected.rev !== undefined) {
    assert.equal(row.revisionObligation, expected.rev, `${label} revision obligation`);
  }
}

const GROUNDED_LIVE: Expected = {
  rec: ["true", "false"],
  live: ["true", "false"],
  coll: "false",
  status: "Grounded",
  authority: ["Live", null],
  rev: false,
};
const EXCLUDED_LIVE: Expected = {
  rec: ["false", "true"],
  live: ["false", "true"],
  coll: "false",
  status: "Excluded",
  authority: [null, "Live"],
  rev: false,
};
const OPEN: Expected = {
  rec: ["false", "false"],
  live: ["false", "false"],
  coll: "false",
  status: "Open",
  authority: [null, null],
  rev: false,
};

function revisionKeys(model: PiModel): string[] {
  return model.revisionObligations.map((r) => `${r.boundary} ${itemKey(r.item)}`).sort();
}

/** The OverlapUnknown obligations in the model's own order (A28). */
function overlapKeys(model: PiModel): string[] {
  return model.overlapObligations.map((o) => `${o.left} ${o.right} ${itemKey(o.item)}`);
}

function handle(id: string): HandleSpec {
  return { id, criterion: `${id}-criterion`, kind: "structural" };
}

function unary(relation: string, h: string): Item {
  return atom(relation, [{ role: "of", handle: h }]);
}

const A = atom("A");
const C = atom("C");
const E = atom("E");
const P = atom("P");
const Q = atom("Q");
const X = atom("X");

function test_oracle_single_observation(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  const m = evaluatePi({ boundaries: bs, observations: [{ boundary: "B", polarity: "+", item: P }] });

  assert.deepEqual(m.boundaries, [TOP_BOUNDARY, "B"]);
  // ⊥ is always tracked (A22).
  assert.deepEqual(m.universe.map(itemKey).sort(), [itemKey(P), itemKey(bottom())].sort());
  expectRow(m, "B", P, { ...GROUNDED_LIVE, obs: "false" });
  // Heredity runs downward only, so the broader ⊤_B holds no record.
  expectRow(m, TOP_BOUNDARY, P, { ...OPEN, obs: "false" });
  assert.deepEqual(m.revisionObligations, []);
}
test("test_oracle_single_observation", test_oracle_single_observation);

function test_oracle_downward_heredity(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  bs.defineBoundary("B1", { parents: ["B"] });
  bs.defineBoundary("B2", { parents: ["B1"] });
  bs.defineBoundary("S");
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: P },
      { boundary: "B", polarity: "-", item: Q },
    ],
  });

  for (const b of ["B", "B1", "B2"]) {
    expectRow(m, b, P, GROUNDED_LIVE);
    expectRow(m, b, Q, EXCLUDED_LIVE);
  }
  for (const b of [TOP_BOUNDARY, "S"]) {
    expectRow(m, b, P, OPEN);
    expectRow(m, b, Q, OPEN);
  }
}
test("test_oracle_downward_heredity", test_oracle_downward_heredity);

function test_oracle_collision_obstructs_parent_boundary(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  bs.defineBoundary("B1", { parents: ["B"] });
  bs.defineBoundary("B2", { parents: ["B"] });
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: P },
      { boundary: "B1", polarity: "-", item: P },
    ],
  });

  // B1 holds the inherited +P and its own -P: a collision, with neither side Live.
  expectRow(m, "B1", P, {
    rec: ["true", "true"],
    live: ["false", "false"],
    coll: "true",
    obs: "true",
    status: "Collision",
    authority: ["Quarantined", "Quarantined"],
    rev: true,
  });
  // The broad ground on B keeps its record but is obstructed by its sub-boundary B1.
  expectRow(m, "B", P, {
    rec: ["true", "false"],
    live: ["false", "false"],
    coll: "false",
    obs: "true",
    status: "Grounded",
    authority: ["Quarantined", null],
    rev: false,
  });
  // The sibling B2 is unobstructed, but its record descends from the obstructed ground on B.
  expectRow(m, "B2", P, {
    rec: ["true", "false"],
    live: ["false", "false"],
    obs: "false",
    status: "Grounded",
    authority: ["Quarantined", null],
    rev: false,
  });
  expectRow(m, TOP_BOUNDARY, P, { ...OPEN, obs: "true" });
  assert.deepEqual(revisionKeys(m), [`B1 ${itemKey(P)}`]);
}
test("test_oracle_collision_obstructs_parent_boundary", test_oracle_collision_obstructs_parent_boundary);

function test_oracle_ghost_collision_from_obstructed_antecedent(): void {
  // Broad conditional X → A on B, a local counterexample -X to its antecedent on B1 ⊑ B,
  // and an independent exclusion -A on B.
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  bs.defineBoundary("B1", { parents: ["B"] });
  const conditional = implies(X, A);
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: conditional },
      { boundary: "B", polarity: "+", item: X },
      { boundary: "B1", polarity: "-", item: X },
      { boundary: "B", polarity: "-", item: A },
    ],
  });

  expectRow(m, "B1", X, { status: "Collision", coll: "true", rev: true });
  expectRow(m, "B", X, { status: "Grounded", authority: ["Quarantined", null], obs: "true" });
  // Scoped Cut needs a Live +X, so no +A is fabricated against the independent -A.
  for (const b of ["B", "B1"]) {
    expectRow(m, b, A, { ...EXCLUDED_LIVE, obs: "false" });
    expectRow(m, b, conditional, GROUNDED_LIVE);
  }
  expectRow(m, TOP_BOUNDARY, A, OPEN);
  assert.deepEqual(revisionKeys(m), [`B1 ${itemKey(X)}`]);
}
test(
  "test_oracle_ghost_collision_from_obstructed_antecedent",
  test_oracle_ghost_collision_from_obstructed_antecedent,
);

function test_oracle_falsified_conditional_fabricates_no_ghost_collision(): void {
  // X → A on B is refuted on B1 by +X ∧ -A; on B2 the antecedent +X holds next to an
  // exclusion -A. The refuted conditional must not derive +A on B2.
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  bs.defineBoundary("B1", { parents: ["B"] });
  bs.defineBoundary("B2", { parents: ["B"] });
  bs.declareDisjoint("B1", "B2");
  const conditional = implies(X, A);
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: conditional },
      { boundary: "B1", polarity: "+", item: X },
      { boundary: "B1", polarity: "-", item: A },
      { boundary: "B2", polarity: "+", item: X },
      { boundary: "B2", polarity: "-", item: A },
    ],
  });

  for (const b of ["B1", "B2"]) {
    // Counterexample: record -(X → A) from record -A and Live +X; it meets the inherited
    // +(X → A), so the conditional collides here and is obstructed on B.
    expectRow(m, b, conditional, {
      rec: ["true", "true"],
      live: ["false", "false"],
      coll: "true",
      status: "Collision",
      authority: ["Quarantined", "Quarantined"],
      rev: true,
    });
    expectRow(m, b, X, GROUNDED_LIVE);
    expectRow(m, b, A, { ...EXCLUDED_LIVE, obs: "false" });
  }
  expectRow(m, "B", conditional, {
    rec: ["true", "false"],
    live: ["false", "false"],
    obs: "true",
    status: "Grounded",
    authority: ["Quarantined", null],
  });
  expectRow(m, "B", A, OPEN);
  assert.deepEqual(revisionKeys(m), [`B1 ${itemKey(conditional)}`, `B2 ${itemKey(conditional)}`]);
}
test(
  "test_oracle_falsified_conditional_fabricates_no_ghost_collision",
  test_oracle_falsified_conditional_fabricates_no_ghost_collision,
);

function test_oracle_symmetric_incompatibility_conflict(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: A },
      { boundary: "B", polarity: "+", item: C },
    ],
    incompatibilities: [{ boundary: "B", left: A, right: C }],
  });

  // live(B,+,A) ← not obs(B,A) ← coll(B,A) ← rec(B,-,A) ← live(B,+,C) ← not obs(B,C) ← … :
  // an even loop through negation, so the well-founded model leaves it undefined. Under G4b
  // the undefined exclusion record is possible but not present, so it has no authority; the
  // undefined coll still reports Collision, and each side's observed record is Undetermined.
  for (const item of [A, C]) {
    expectRow(m, "B", item, {
      rec: ["true", "undefined"],
      live: ["undefined", "undefined"],
      coll: "undefined",
      obs: "undefined",
      status: "Collision",
      authority: ["Undetermined", null],
      rev: true,
    });
    expectRow(m, TOP_BOUNDARY, item, { ...OPEN, obs: "undefined" });
  }
  assert.deepEqual(revisionKeys(m), [`B ${itemKey(A)}`, `B ${itemKey(C)}`]);
}
test("test_oracle_symmetric_incompatibility_conflict", test_oracle_symmetric_incompatibility_conflict);

function test_oracle_mutual_support_cycle_grounds_nothing(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: implies(A, C) },
      { boundary: "B", polarity: "+", item: implies(C, A) },
    ],
  });

  // +A needs a Live +C and +C needs a Live +A; the least model gives neither.
  for (const item of [A, C]) {
    expectRow(m, "B", item, OPEN);
  }
  expectRow(m, "B", implies(A, C), GROUNDED_LIVE);
  expectRow(m, "B", implies(C, A), GROUNDED_LIVE);
  assert.deepEqual(m.revisionObligations, []);
}
test("test_oracle_mutual_support_cycle_grounds_nothing", test_oracle_mutual_support_cycle_grounds_nothing);

function emptyRestrictedUniversalSystem(): BoundarySystem {
  const bs = new BoundarySystem();
  bs.defineBoundary("D", { handles: [handle("a"), handle("b")] });
  return bs;
}

// ∀(x : D ⊓ [Q(x)]) P(x), evaluated on D, with Dom(D) = {a, b}.
const restrictedUniversal = forall("x", "D", unary("P", "x"), unary("Q", "x"));

function test_oracle_empty_restricted_universal_on_closed_domain(): void {
  const exclusions = [
    { boundary: "D", polarity: "-" as const, item: unary("Q", "a") },
    { boundary: "D", polarity: "-" as const, item: unary("Q", "b") },
  ];
  const m = evaluatePi({
    boundaries: emptyRestrictedUniversalSystem(),
    observations: exclusions,
    closedDomains: ["D"],
    queries: [restrictedUniversal],
  });

  // ∀ generic: every handle carries a Live -δ(w), so the universal holds vacuously.
  expectRow(m, "D", restrictedUniversal, GROUNDED_LIVE);
  // ∀E needs a Live +δ(w), which no handle has.
  expectRow(m, "D", unary("P", "a"), OPEN);
  expectRow(m, "D", unary("P", "b"), OPEN);
  // The exclusions sit on D only, so ⊤_B has no support.
  expectRow(m, TOP_BOUNDARY, restrictedUniversal, OPEN);

  // The support is the -δ exclusions: without -Q(b) the universal stays Open …
  const partial = evaluatePi({
    boundaries: emptyRestrictedUniversalSystem(),
    observations: exclusions.slice(0, 1),
    closedDomains: ["D"],
    queries: [restrictedUniversal],
  });
  expectRow(partial, "D", restrictedUniversal, OPEN);

  // … and a quarantined -Q(b) (colliding with +Q(b)) supports nothing either.
  const quarantined = evaluatePi({
    boundaries: emptyRestrictedUniversalSystem(),
    observations: [...exclusions, { boundary: "D", polarity: "+", item: unary("Q", "b") }],
    closedDomains: ["D"],
    queries: [restrictedUniversal],
  });
  expectRow(quarantined, "D", unary("Q", "b"), { status: "Collision", rev: true });
  expectRow(quarantined, "D", restrictedUniversal, OPEN);
}
test(
  "test_oracle_empty_restricted_universal_on_closed_domain",
  test_oracle_empty_restricted_universal_on_closed_domain,
);

function test_oracle_empty_restricted_universal_on_unclosed_domain(): void {
  const m = evaluatePi({
    boundaries: emptyRestrictedUniversalSystem(),
    observations: [
      { boundary: "D", polarity: "-", item: unary("Q", "a") },
      { boundary: "D", polarity: "-", item: unary("Q", "b") },
    ],
    queries: [restrictedUniversal],
  });

  // Without CloseDomain(D), enumeration never grounds +∀, and no counterexample exists.
  expectRow(m, "D", restrictedUniversal, OPEN);
}
test(
  "test_oracle_empty_restricted_universal_on_unclosed_domain",
  test_oracle_empty_restricted_universal_on_unclosed_domain,
);

function test_oracle_existential_exclusion_and_introduction(): void {
  const bs = (): BoundarySystem => emptyRestrictedUniversalSystem();
  const existential = exists("x", "D", unary("P", "x"));
  const exclusions = [
    { boundary: "D", polarity: "-" as const, item: unary("P", "a") },
    { boundary: "D", polarity: "-" as const, item: unary("P", "b") },
  ];

  const closed = evaluatePi({
    boundaries: bs(),
    observations: exclusions,
    closedDomains: ["D"],
    queries: [existential],
  });
  expectRow(closed, "D", existential, EXCLUDED_LIVE);

  const unclosed = evaluatePi({ boundaries: bs(), observations: exclusions, queries: [existential] });
  expectRow(unclosed, "D", existential, OPEN);

  // ∃I is open-world: one Live witness suffices without a closure.
  const witnessed = evaluatePi({
    boundaries: bs(),
    observations: [{ boundary: "D", polarity: "+", item: unary("P", "a") }],
    queries: [existential],
  });
  expectRow(witnessed, "D", existential, GROUNDED_LIVE);

  // The exclusion takes the body's exclusion records as record premises: a collided -P(b)
  // still yields the record of -∃, but not its authority.
  const collided = evaluatePi({
    boundaries: bs(),
    observations: [...exclusions, { boundary: "D", polarity: "+", item: unary("P", "b") }],
    closedDomains: ["D"],
    queries: [existential],
  });
  expectRow(collided, "D", existential, {
    rec: ["false", "true"],
    live: ["false", "false"],
    coll: "false",
    status: "Excluded",
    authority: [null, "Quarantined"],
    rev: false,
  });
}
test("test_oracle_existential_exclusion_and_introduction", test_oracle_existential_exclusion_and_introduction);

function test_oracle_scoped_cut_fires_on_meet(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B1");
  bs.defineBoundary("B2");
  bs.defineBoundary("M", { parents: ["B1", "B2"] });
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B1", polarity: "+", item: A },
      { boundary: "B2", polarity: "+", item: implies(A, C) },
    ],
  });

  expectRow(m, "M", C, GROUNDED_LIVE);
  for (const b of [TOP_BOUNDARY, "B1", "B2"]) {
    expectRow(m, b, C, OPEN);
  }
}
test("test_oracle_scoped_cut_fires_on_meet", test_oracle_scoped_cut_fires_on_meet);

function test_oracle_cover_disjunction_and_gluing(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  bs.defineBoundary("B1", { parents: ["B"] });
  bs.defineBoundary("B2", { parents: ["B"] });
  bs.declareDisjoint("B1", "B2");
  bs.registerCover("B", ["B1", "B2"]);
  const disjunction = or(A, C);
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B1", polarity: "+", item: A },
      { boundary: "B2", polarity: "+", item: C },
      { boundary: "B1", polarity: "+", item: E },
      { boundary: "B2", polarity: "+", item: E },
    ],
    queries: [disjunction],
  });

  expectRow(m, "B", disjunction, GROUNDED_LIVE);
  expectRow(m, "B", E, GROUNDED_LIVE);
  expectRow(m, "B", A, OPEN);
  expectRow(m, "B", C, OPEN);
  expectRow(m, "B1", disjunction, GROUNDED_LIVE);
  expectRow(m, TOP_BOUNDARY, disjunction, OPEN);
  expectRow(m, TOP_BOUNDARY, E, OPEN);
}
test("test_oracle_cover_disjunction_and_gluing", test_oracle_cover_disjunction_and_gluing);

function test_oracle_congruence_on_native_relation(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("D", { handles: [handle("a"), handle("b")], nativeRelations: ["R"] });
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "D", polarity: "+", item: equiv("D", "a", "b") },
      { boundary: "D", polarity: "+", item: unary("R", "a") },
      { boundary: "D", polarity: "+", item: unary("S", "a") },
    ],
  });

  expectRow(m, "D", unary("R", "b"), GROUNDED_LIVE);
  // S is not native to D, so congruence does not rewrite it.
  expectRow(m, "D", unary("S", "b"), OPEN);
  expectRow(m, "D", equiv("D", "b", "a"), GROUNDED_LIVE);
  expectRow(m, "D", equiv("D", "a", "a"), GROUNDED_LIVE);
  expectRow(m, TOP_BOUNDARY, unary("R", "b"), OPEN);
}
test("test_oracle_congruence_on_native_relation", test_oracle_congruence_on_native_relation);

function test_oracle_structural_collapse(): void {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  const m = evaluatePi({ boundaries: bs, observations: [], collapses: [{ boundary: "B", item: A }] });

  expectRow(m, "B", implies(A, bottom()), GROUNDED_LIVE);
  expectRow(m, "B", A, EXCLUDED_LIVE);
  expectRow(m, "B", bottom(), EXCLUDED_LIVE);
  expectRow(m, TOP_BOUNDARY, bottom(), EXCLUDED_LIVE);
  expectRow(m, TOP_BOUNDARY, A, OPEN);
}
test("test_oracle_structural_collapse", test_oracle_structural_collapse);

function test_oracle_nested_polarity_flips_belong_to_universe(): void {
  // A3 as amended by item 14: a flip belongs to U(Σ, Q) whenever it arises as a sub-item or a
  // quantifier instance; U(Σ, Q) is only not closed under prefixing `~`.
  const singleBoundary = (): BoundarySystem => {
    const system = new BoundarySystem();
    system.defineBoundary("B");
    return system;
  };
  const observations = [
    { boundary: "B", polarity: "-" as const, item: P },
    { boundary: "B", polarity: "+" as const, item: Q },
  ];

  const queried = evaluatePi({ boundaries: singleBoundary(), observations, queries: [flip(P)] });
  expectRow(queried, "B", flip(P), GROUNDED_LIVE);

  // ~P nested in a queried conjunction belongs to U(Σ, Q): +~P from the record -P, then ∧I.
  const conjunction = and(Q, flip(P));
  const nested = evaluatePi({ boundaries: singleBoundary(), observations, queries: [conjunction] });
  expectRow(nested, "B", flip(P), GROUNDED_LIVE);
  expectRow(nested, "B", conjunction, GROUNDED_LIVE);

  // No flip is prefixed to tracked items: without a query, ~P and ~Q are not in U(Σ, Q),
  // which holds only P, Q and the always-tracked ⊥.
  const plain = evaluatePi({ boundaries: singleBoundary(), observations });
  assert.deepEqual(
    plain.universe.map(itemKey).sort(),
    [itemKey(P), itemKey(Q), itemKey(bottom())].sort(),
  );
  assert.throws(() => plain.at("B", flip(P)), /outside/);

  // Flipped quantifier instances ~P(a), ~P(b) belong to U(Σ, Q), so ∀ generic can use them.
  const bs = new BoundarySystem();
  bs.defineBoundary("D", { handles: [handle("a"), handle("b")] });
  const universal = forall("x", "D", flip(unary("P", "x")));
  const instances = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "D", polarity: "-", item: unary("P", "a") },
      { boundary: "D", polarity: "-", item: unary("P", "b") },
    ],
    closedDomains: ["D"],
    queries: [universal],
  });
  expectRow(instances, "D", flip(unary("P", "a")), GROUNDED_LIVE);
  expectRow(instances, "D", universal, GROUNDED_LIVE);
}
test(
  "test_oracle_nested_polarity_flips_belong_to_universe",
  test_oracle_nested_polarity_flips_belong_to_universe,
);

function test_oracle_undefined_record_is_possible_but_not_present(): void {
  // G4b: the symmetric conflict A ⊥_B C leaves live(B,+,C) undefined, so the exclusion of G
  // inferred from it through C ⊥_B G is undefined. With no positive record, coll(B, G) is
  // false, and the merely possible exclusion supports no status.
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  const G = atom("G");
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "B", polarity: "+", item: A },
      { boundary: "B", polarity: "+", item: C },
    ],
    incompatibilities: [
      { boundary: "B", left: A, right: C },
      { boundary: "B", left: C, right: G },
    ],
  });

  expectRow(m, "B", G, {
    rec: ["false", "undefined"],
    live: ["false", "undefined"],
    coll: "false",
    obs: "false",
    status: "Open",
    authority: [null, null],
    rev: false,
  });
  expectRow(m, "B", C, { status: "Collision", authority: ["Undetermined", null], rev: true });
}
test(
  "test_oracle_undefined_record_is_possible_but_not_present",
  test_oracle_undefined_record_is_possible_but_not_present,
);

function test_oracle_congruence_rewrites_one_occurrence_at_a_time(): void {
  // A6 as amended by item 14: from R(a, a) and a ≈_D b, congruence rewrites one occurrence,
  // giving R(a, b) and R(b, a); rewriting again gives R(b, b).
  const bs = new BoundarySystem();
  bs.defineBoundary("D", { handles: [handle("a"), handle("b")], nativeRelations: ["R"] });
  const binary = (first: string, second: string): Item =>
    atom("R", [
      { role: "first", handle: first },
      { role: "second", handle: second },
    ]);
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "D", polarity: "+", item: equiv("D", "a", "b") },
      { boundary: "D", polarity: "+", item: binary("a", "a") },
    ],
  });

  expectRow(m, "D", binary("a", "b"), GROUNDED_LIVE);
  expectRow(m, "D", binary("b", "a"), GROUNDED_LIVE);
  expectRow(m, "D", binary("b", "b"), GROUNDED_LIVE);
  expectRow(m, TOP_BOUNDARY, binary("a", "b"), OPEN);
}
test(
  "test_oracle_congruence_rewrites_one_occurrence_at_a_time",
  test_oracle_congruence_rewrites_one_occurrence_at_a_time,
);

function test_oracle_vacuous_grounding_requires_non_bottom_domain(): void {
  // A13 as amended by item 14: ∀ generic and the ∃ exclusion need CloseDomain(D) and D ≠ ⊥_B.
  const bs = new BoundarySystem();
  bs.defineBoundary("E0", { handles: [] });
  const emptyUniversal = forall("x", "E0", unary("P", "x"));
  const emptyExistential = exists("x", "E0", unary("P", "x"));
  const bottomUniversal = forall("x", BOT_BOUNDARY, unary("P", "x"));
  const bottomExistential = exists("x", BOT_BOUNDARY, unary("P", "x"));
  const m = evaluatePi({
    boundaries: bs,
    observations: [],
    closedDomains: ["E0", BOT_BOUNDARY],
    queries: [emptyUniversal, emptyExistential, bottomUniversal, bottomExistential],
  });

  for (const b of [TOP_BOUNDARY, "E0"]) {
    // A closed, empty, non-bottom domain: vacuous truth grounded by the closure alone.
    expectRow(m, b, emptyUniversal, GROUNDED_LIVE);
    expectRow(m, b, emptyExistential, EXCLUDED_LIVE);
    // A closure listed for ⊥_B grounds nothing.
    expectRow(m, b, bottomUniversal, OPEN);
    expectRow(m, b, bottomExistential, OPEN);
  }
}
test(
  "test_oracle_vacuous_grounding_requires_non_bottom_domain",
  test_oracle_vacuous_grounding_requires_non_bottom_domain,
);

function test_oracle_retracted_observation_keeps_its_item(): void {
  // A23: the observation +(P ∧ R) on B was retracted; its item is passed as a history item.
  // It stays tracked, so it and its sub-items belong to U(Σ, Q), but it supplies no record.
  const R = atom("R");
  const retracted = and(P, R);
  const singleBoundary = (): BoundarySystem => {
    const system = new BoundarySystem();
    system.defineBoundary("B");
    return system;
  };

  const m = evaluatePi({
    boundaries: singleBoundary(),
    observations: [{ boundary: "B", polarity: "+", item: Q }],
    historyItems: [retracted],
  });
  for (const b of [TOP_BOUNDARY, "B"]) {
    expectRow(m, b, retracted, { ...OPEN, obs: "false" });
    expectRow(m, b, P, OPEN);
    expectRow(m, b, R, OPEN);
  }
  expectRow(m, "B", Q, GROUNDED_LIVE);

  // Without the history item, the retracted item is outside U(Σ, Q).
  const forgotten = evaluatePi({
    boundaries: singleBoundary(),
    observations: [{ boundary: "B", polarity: "+", item: Q }],
  });
  assert.throws(() => forgotten.at("B", retracted), /outside/);

  // A history item still takes records that current grounds derive: ∧I from +P and +R.
  const rederived = evaluatePi({
    boundaries: singleBoundary(),
    observations: [
      { boundary: "B", polarity: "+", item: P },
      { boundary: "B", polarity: "+", item: R },
    ],
    historyItems: [retracted],
  });
  expectRow(rederived, "B", retracted, GROUNDED_LIVE);
}
test("test_oracle_retracted_observation_keeps_its_item", test_oracle_retracted_observation_keeps_its_item);

function test_oracle_bottom_is_always_tracked(): void {
  // A22: ⊥ belongs to U(Σ, Q) in every state, with its structural exclusion on every boundary.
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  const m = evaluatePi({ boundaries: bs, observations: [{ boundary: "B", polarity: "+", item: P }] });

  assert.ok(m.universe.some((item) => item.kind === "bottom"), "⊥ ∈ U(Σ, Q)");
  for (const b of [TOP_BOUNDARY, "B"]) {
    expectRow(m, b, bottom(), { ...EXCLUDED_LIVE, obs: "false" });
  }
  assert.deepEqual(m.revisionObligations, []);

  // Even a state with no observations at all tracks ⊥.
  const empty = evaluatePi({ boundaries: bs, observations: [] });
  assert.deepEqual(empty.universe.map(itemKey), [itemKey(bottom())]);
  expectRow(empty, "B", bottom(), EXCLUDED_LIVE);
}
test("test_oracle_bottom_is_always_tracked", test_oracle_bottom_is_always_tracked);

// ---------------------------------------------------------------------------------------------
// The three-valued meet of item 4 (main commit 5a385ce): Lab and Field below ⊤_B share no
// registered sub-boundary and no declared disjointness, so their overlap is unknown.

function labAndField(): BoundarySystem {
  const bs = new BoundarySystem();
  bs.defineBoundary("Lab");
  bs.defineBoundary("Field");
  return bs;
}

function test_oracle_scoped_cut_needs_known_overlap(): void {
  const observations = [
    { boundary: "Lab", polarity: "+" as const, item: A },
    { boundary: "Field", polarity: "+" as const, item: implies(A, C) },
  ];

  // Unknown overlap: Scoped Cut has no conclusion boundary, so +C appears nowhere.
  const unknown = evaluatePi({ boundaries: labAndField(), observations });
  for (const b of [TOP_BOUNDARY, "Lab", "Field"]) {
    expectRow(unknown, b, C, OPEN);
  }
  expectRow(unknown, "Lab", A, GROUNDED_LIVE);
  expectRow(unknown, "Field", implies(A, C), GROUNDED_LIVE);
  assert.deepEqual(overlapKeys(unknown), []);

  // Declared disjointness licenses nothing either.
  const disjointSystem = labAndField();
  disjointSystem.declareDisjoint("Lab", "Field");
  const disjoint = evaluatePi({ boundaries: disjointSystem, observations });
  for (const b of [TOP_BOUNDARY, "Lab", "Field"]) {
    expectRow(disjoint, b, C, OPEN);
  }

  // A registered common sub-boundary makes the overlap known, and the cut fires there.
  const knownSystem = labAndField();
  knownSystem.defineBoundary("LabField", { parents: ["Lab", "Field"] });
  const known = evaluatePi({ boundaries: knownSystem, observations });
  expectRow(known, "LabField", C, GROUNDED_LIVE);
  for (const b of [TOP_BOUNDARY, "Lab", "Field"]) {
    expectRow(known, b, C, OPEN);
  }
}
test("test_oracle_scoped_cut_needs_known_overlap", test_oracle_scoped_cut_needs_known_overlap);

function test_oracle_unknown_overlap_records_obligation_without_collision(): void {
  // -P on Lab and +P on Field: no boundary holds both records, so nothing collides, both records
  // stay Live, and the conflict is reported as OverlapUnknown(Lab, Field, P). Lab precedes Field
  // in 𝔅(Σ), so it is the left boundary although it holds the exclusion (A28).
  const m = evaluatePi({
    boundaries: labAndField(),
    observations: [
      { boundary: "Lab", polarity: "-", item: P },
      { boundary: "Field", polarity: "+", item: P },
    ],
  });

  expectRow(m, "Lab", P, { ...EXCLUDED_LIVE, obs: "false" });
  expectRow(m, "Field", P, { ...GROUNDED_LIVE, obs: "false" });
  expectRow(m, TOP_BOUNDARY, P, { ...OPEN, obs: "false" });
  assert.deepEqual(m.boundaries, [TOP_BOUNDARY, "Lab", "Field"]);
  assert.deepEqual(m.revisionObligations, []);
  assert.deepEqual(m.overlapObligations, [{ left: "Lab", right: "Field", item: P }]);
}
test(
  "test_oracle_unknown_overlap_records_obligation_without_collision",
  test_oracle_unknown_overlap_records_obligation_without_collision,
);

function test_oracle_declared_disjointness_raises_no_obligation(): void {
  const bs = labAndField();
  bs.declareDisjoint("Lab", "Field");
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "Lab", polarity: "+", item: P },
      { boundary: "Field", polarity: "-", item: P },
    ],
  });

  expectRow(m, "Lab", P, { ...GROUNDED_LIVE, obs: "false" });
  expectRow(m, "Field", P, { ...EXCLUDED_LIVE, obs: "false" });
  expectRow(m, TOP_BOUNDARY, P, { ...OPEN, obs: "false" });
  assert.deepEqual(m.revisionObligations, []);
  assert.deepEqual(m.overlapObligations, []);
}
test(
  "test_oracle_declared_disjointness_raises_no_obligation",
  test_oracle_declared_disjointness_raises_no_obligation,
);

function test_oracle_registered_common_sub_boundary_collides_instead(): void {
  // Defining LabField below both makes the overlap known (audit reproduction R3): heredity
  // brings +P and -P together on LabField, which collides and obstructs both broad grounds.
  const bs = labAndField();
  bs.defineBoundary("LabField", { parents: ["Lab", "Field"] });
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "Lab", polarity: "+", item: P },
      { boundary: "Field", polarity: "-", item: P },
    ],
  });

  expectRow(m, "LabField", P, {
    rec: ["true", "true"],
    live: ["false", "false"],
    coll: "true",
    obs: "true",
    status: "Collision",
    authority: ["Quarantined", "Quarantined"],
    rev: true,
  });
  expectRow(m, "Lab", P, {
    rec: ["true", "false"],
    live: ["false", "false"],
    coll: "false",
    obs: "true",
    status: "Grounded",
    authority: ["Quarantined", null],
    rev: false,
  });
  expectRow(m, "Field", P, {
    rec: ["false", "true"],
    live: ["false", "false"],
    coll: "false",
    obs: "true",
    status: "Excluded",
    authority: [null, "Quarantined"],
    rev: false,
  });
  expectRow(m, TOP_BOUNDARY, P, { ...OPEN, obs: "true" });
  assert.deepEqual(revisionKeys(m), [`LabField ${itemKey(P)}`]);
  assert.deepEqual(m.overlapObligations, []);
}
test(
  "test_oracle_registered_common_sub_boundary_collides_instead",
  test_oracle_registered_common_sub_boundary_collides_instead,
);

function test_oracle_overlap_obligations_follow_present_records(): void {
  // A29, A30. -P on ⊤_B and +P on Lab, with Lab1 ⊑ Lab declared after Field. Heredity puts -P
  // on every boundary and +P on Lab1, so Lab and Lab1 collide and every record of P is
  // Quarantined. ⊤_B is known to overlap every boundary, so its -P raises no obligation; the
  // unknown pairs (Lab, Field) and (Field, Lab1) each do, through inherited and quarantined
  // records and next to the collisions, which keep their own Rev(B, P).
  const chain = labAndField();
  chain.defineBoundary("Lab1", { parents: ["Lab"] });
  const m = evaluatePi({
    boundaries: chain,
    observations: [
      { boundary: TOP_BOUNDARY, polarity: "-", item: P },
      { boundary: "Lab", polarity: "+", item: P },
    ],
  });

  for (const b of ["Lab", "Lab1"]) {
    expectRow(m, b, P, { status: "Collision", authority: ["Quarantined", "Quarantined"], rev: true });
  }
  expectRow(m, "Field", P, {
    rec: ["false", "true"],
    live: ["false", "false"],
    obs: "false",
    status: "Excluded",
    authority: [null, "Quarantined"],
    rev: false,
  });
  expectRow(m, TOP_BOUNDARY, P, { status: "Excluded", authority: [null, "Quarantined"], obs: "true" });
  assert.deepEqual(m.boundaries, [TOP_BOUNDARY, "Lab", "Field", "Lab1"]);
  assert.deepEqual(revisionKeys(m), [`Lab ${itemKey(P)}`, `Lab1 ${itemKey(P)}`]);
  assert.deepEqual(overlapKeys(m), [`Lab Field ${itemKey(P)}`, `Field Lab1 ${itemKey(P)}`]);

  // A merely possible record raises no obligation. The symmetric conflict A ⊥_Lab C leaves
  // live(Lab, +, A) and live(Lab, +, C) undefined, so ∧I gives +(A ∧ C) on Lab an undefined
  // record, while Field holds a present -(A ∧ C).
  const conjunction = and(A, C);
  const possible = evaluatePi({
    boundaries: labAndField(),
    observations: [
      { boundary: "Lab", polarity: "+", item: A },
      { boundary: "Lab", polarity: "+", item: C },
      { boundary: "Field", polarity: "-", item: conjunction },
    ],
    incompatibilities: [{ boundary: "Lab", left: A, right: C }],
  });
  expectRow(possible, "Lab", conjunction, {
    rec: ["undefined", "undefined"],
    coll: "undefined",
    status: "Collision",
    authority: [null, null],
    rev: true,
  });
  expectRow(possible, "Field", conjunction, { ...EXCLUDED_LIVE, obs: "false" });
  assert.deepEqual(possible.overlapObligations, []);
}
test(
  "test_oracle_overlap_obligations_follow_present_records",
  test_oracle_overlap_obligations_follow_present_records,
);

function test_oracle_ambiguous_meet_is_an_error_where_needed(): void {
  // A11, A31. M1 and M2 are two maximal common sub-boundaries of Lab and Field, so their meet
  // is ambiguous until a meet is registered.
  const ambiguous = (): BoundarySystem => {
    const bs = labAndField();
    bs.defineBoundary("M1", { parents: ["Lab", "Field"] });
    bs.defineBoundary("M2", { parents: ["Lab", "Field"] });
    return bs;
  };

  // Scoped Cut needs every pair's meet once U(Σ, Q) holds an implication.
  assert.throws(
    () => evaluatePi({ boundaries: ambiguous(), observations: [], queries: [implies(A, C)] }),
    /Scoped Cut needs the meet of "Lab" and "Field", which is ambiguous/,
  );
  // The reporting needs the status of a pair holding opposite present records.
  assert.throws(
    () =>
      evaluatePi({
        boundaries: ambiguous(),
        observations: [
          { boundary: "Lab", polarity: "+", item: P },
          { boundary: "Field", polarity: "-", item: P },
        ],
      }),
    /reporting OverlapUnknown needs the meet of "Lab" and "Field", which is ambiguous/,
  );
  // Otherwise the ambiguous pair is never classified.
  const m = evaluatePi({
    boundaries: ambiguous(),
    observations: [{ boundary: "Lab", polarity: "+", item: P }],
  });
  for (const b of ["Lab", "M1", "M2"]) {
    expectRow(m, b, P, GROUNDED_LIVE);
  }
  assert.deepEqual(m.overlapObligations, []);

  // Registering the meet removes the ambiguity: the conflict collides on M, M1 and M2, and the
  // known overlap of Lab and Field raises no obligation. M, M1 and M2 are pairwise of unknown
  // overlap and each holds both records, so each of their pairs carries one (A29).
  const resolvedSystem = ambiguous();
  resolvedSystem.defineBoundary("M", { parents: ["Lab", "Field"] });
  resolvedSystem.defineMeet("Lab", "Field", "M");
  const resolved = evaluatePi({
    boundaries: resolvedSystem,
    observations: [
      { boundary: "Lab", polarity: "+", item: P },
      { boundary: "Field", polarity: "-", item: P },
    ],
  });
  assert.deepEqual(revisionKeys(resolved), [`M ${itemKey(P)}`, `M1 ${itemKey(P)}`, `M2 ${itemKey(P)}`]);
  assert.deepEqual(overlapKeys(resolved), [
    `M1 M2 ${itemKey(P)}`,
    `M1 M ${itemKey(P)}`,
    `M2 M ${itemKey(P)}`,
  ]);
}
test("test_oracle_ambiguous_meet_is_an_error_where_needed", test_oracle_ambiguous_meet_is_an_error_where_needed);

// ---------------------------------------------------------------------------------------------
// Cover validity, witnessed covers and Withdraw (items 5, 7 and 14 as amended in main commits
// fde28ec and a7377cf). The oracle judges every registered cover itself (A33–A38).

/** Every witnessed cover of the model as "boundary: {cells}", sorted. */
function coverKeys(model: PiModel): string[] {
  return model.witnessedCovers.map((c) => `${c.boundary}: {${c.cells.join(", ")}}`).sort();
}

/** The cell lists of the witnessed covers of one boundary, sorted. */
function coversOf(model: PiModel, boundary: string): string[] {
  return model.witnessedCovers
    .filter((c) => c.boundary === boundary)
    .map((c) => c.cells.join(", "))
    .sort();
}

/** Two cells C1, C2 ⊑ B declared disjoint; the callers register {C1, C2} ▷ B. */
function twoCellCover(): BoundarySystem {
  const bs = new BoundarySystem();
  bs.defineBoundary("B");
  bs.defineBoundary("C1", { parents: ["B"] });
  bs.defineBoundary("C2", { parents: ["B"] });
  bs.declareDisjoint("C1", "C2");
  return bs;
}

function test_oracle_invalid_cover_is_order_independent(): void {
  // Audit reproduction R2: B3 ⊑ B is declared disjoint from both cells of {C1, C2} ▷ B, so the
  // cover is invalid (Axioms 3 and 5 together) and witnesses nothing, whichever came first.
  const addB3 = (bs: BoundarySystem): void => {
    bs.defineBoundary("B3", { parents: ["B"] });
    bs.declareDisjoint("B3", "C1");
    bs.declareDisjoint("B3", "C2");
  };
  const coverFirst = twoCellCover();
  coverFirst.registerCover("B", ["C1", "C2"], "cover-B");
  addB3(coverFirst);
  const boundaryFirst = twoCellCover();
  addB3(boundaryFirst);
  boundaryFirst.registerCover("B", ["C1", "C2"], "cover-B");

  const disjunction = or(P, Q);
  const observations = [
    { boundary: "C1", polarity: "+" as const, item: P },
    { boundary: "C2", polarity: "+" as const, item: Q },
    { boundary: "B3", polarity: "-" as const, item: P },
    { boundary: "B3", polarity: "-" as const, item: Q },
  ];
  const evaluate = (bs: BoundarySystem): PiModel =>
    evaluatePi({ boundaries: bs, observations, queries: [disjunction] });
  const first = evaluate(coverFirst);
  const second = evaluate(boundaryFirst);

  for (const m of [first, second]) {
    assert.deepEqual(m.coverObligations, [
      { id: "cover-B", target: "B", cells: ["C1", "C2"], validity: "invalid", subBoundaries: ["B3"] },
    ]);
    // Only the identity covers remain: no cover is derived from an invalid one.
    assert.deepEqual(
      coverKeys(m),
      ["B3: {B3}", "B: {B}", "C1: {C1}", "C2: {C2}", `${TOP_BOUNDARY}: {${TOP_BOUNDARY}}`].sort(),
    );
    // No ∨ by cover on B, so B holds no +(P ∨ Q) for B3 to inherit: B3's exclusion of the
    // disjunction (from -P and -Q) stands alone, and nothing collides.
    expectRow(m, "B", disjunction, { ...OPEN, obs: "false" });
    expectRow(m, "B3", disjunction, { ...EXCLUDED_LIVE, obs: "false" });
    expectRow(m, "B3", P, EXCLUDED_LIVE);
    expectRow(m, "B3", Q, EXCLUDED_LIVE);
    expectRow(m, "C1", disjunction, GROUNDED_LIVE);
    expectRow(m, "C2", disjunction, GROUNDED_LIVE);
    expectRow(m, TOP_BOUNDARY, disjunction, OPEN);
    assert.deepEqual(m.revisionObligations, []);
    assert.deepEqual(m.overlapObligations, []);
  }
  // The two registration orders give the same model.
  assert.deepEqual(second.boundaries, first.boundaries);
  assert.deepEqual(second.universe, first.universe);
  assert.deepEqual(second.rows, first.rows);
  assert.deepEqual(second.witnessedCovers, first.witnessedCovers);
  assert.deepEqual(second.coverObligations, first.coverObligations);

  // Before B3 exists the cover is valid and witnesses the disjunction on B.
  const before = twoCellCover();
  before.registerCover("B", ["C1", "C2"], "cover-B");
  const valid = evaluatePi({
    boundaries: before,
    observations: observations.slice(0, 2),
    queries: [disjunction],
  });
  assert.deepEqual(valid.coverObligations, []);
  assert.deepEqual(coversOf(valid, "B"), ["B", "C1, C2"]);
  expectRow(valid, "B", disjunction, GROUNDED_LIVE);

  // Withdrawing the invalid cover discharges its obligation and changes nothing else, since the
  // cover supplied no rule instance.
  assert.equal(coverFirst.withdrawCover("cover-B"), true);
  const withdrawn = evaluate(coverFirst);
  assert.deepEqual(withdrawn.coverObligations, []);
  assert.deepEqual(withdrawn.rows, first.rows);
  assert.deepEqual(withdrawn.witnessedCovers, first.witnessedCovers);
}
test("test_oracle_invalid_cover_is_order_independent", test_oracle_invalid_cover_is_order_independent);

function test_oracle_unverified_cover_still_witnesses(): void {
  // B3 ⊑ B and B4 ⊑ B3 have an unknown overlap with both cells; B5 ⊑ B is disjoint from C1 and
  // of unknown overlap with C2. None is known to overlap a cell and none is disjoint from both,
  // so the cover is unverified and owes an obligation naming the three, but it still witnesses.
  const bs = twoCellCover();
  bs.registerCover("B", ["C1", "C2"], "cover-B");
  bs.defineBoundary("B3", { parents: ["B"] });
  bs.defineBoundary("B4", { parents: ["B3"] });
  bs.defineBoundary("B5", { parents: ["B"] });
  bs.declareDisjoint("B5", "C1");
  const disjunction = or(P, Q);
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "C1", polarity: "+", item: P },
      { boundary: "C2", polarity: "+", item: Q },
      { boundary: "C1", polarity: "+", item: E },
      { boundary: "C2", polarity: "+", item: E },
    ],
    queries: [disjunction],
  });

  assert.deepEqual(m.coverObligations, [
    {
      id: "cover-B",
      target: "B",
      cells: ["C1", "C2"],
      validity: "unverified",
      subBoundaries: ["B3", "B4", "B5"],
    },
  ]);
  // ∨ by cover and Cover-Gluing use the unverified cover; B3, B4 and B5 inherit both records.
  expectRow(m, "B", disjunction, GROUNDED_LIVE);
  expectRow(m, "B", E, GROUNDED_LIVE);
  expectRow(m, "B", P, OPEN);
  for (const b of ["B3", "B4", "B5"]) {
    expectRow(m, b, disjunction, GROUNDED_LIVE);
    expectRow(m, b, E, GROUNDED_LIVE);
    expectRow(m, b, P, OPEN);
    // A cell of unknown overlap blocks the base change: only the identity cover remains.
    assert.deepEqual(coversOf(m, b), [b]);
  }
  assert.deepEqual(coversOf(m, "B"), ["B", "C1, C2"]);
  assert.deepEqual(m.revisionObligations, []);
  assert.deepEqual(m.overlapObligations, []);
}
test("test_oracle_unverified_cover_still_witnesses", test_oracle_unverified_cover_still_witnesses);

function test_oracle_settled_overlap_validates_cover_and_enables_base_change(): void {
  // Stage 1: B3 ⊑ B has an unknown overlap with both cells, so the cover is unverified.
  const bs = twoCellCover();
  bs.registerCover("B", ["C1", "C2"], "cover-B");
  bs.defineBoundary("B3", { parents: ["B"] });
  const unverified = evaluatePi({ boundaries: bs, observations: [] });
  assert.deepEqual(unverified.coverObligations, [
    { id: "cover-B", target: "B", cells: ["C1", "C2"], validity: "unverified", subBoundaries: ["B3"] },
  ]);
  assert.deepEqual(coversOf(unverified, "B3"), ["B3"]);

  // Stage 2: B3C1 below B3 and C1 settles B3 ⊓ C1 as a known overlap, so the cover is valid and
  // its obligation is discharged. The overlap of B3 and C2 is still unknown, so the cover has no
  // base change to B3: a Live +R on B3C1 does not glue to B3.
  const R = atom("R");
  const observations = [{ boundary: "B3C1", polarity: "+" as const, item: R }];
  bs.defineBoundary("B3C1", { parents: ["B3", "C1"] });
  const valid = evaluatePi({ boundaries: bs, observations });
  assert.deepEqual(valid.coverObligations, []);
  assert.deepEqual(coversOf(valid, "B3"), ["B3"]);
  expectRow(valid, "B3C1", R, GROUNDED_LIVE);
  expectRow(valid, "B3", R, OPEN);

  // Stage 3: declaring B3 disjoint from C2 settles the last overlap. The base change
  // {C1 ⊓ B3} = {B3C1} ▷ B3 now exists, and Cover-Gluing lifts +R from B3C1 to B3.
  bs.declareDisjoint("B3", "C2");
  const settled = evaluatePi({ boundaries: bs, observations });
  assert.deepEqual(settled.coverObligations, []);
  assert.deepEqual(coversOf(settled, "B3"), ["B3", "B3C1"]);
  expectRow(settled, "B3", R, GROUNDED_LIVE);
  // Neither C1 nor B is lifted: C1 has no cover by B3C1, and C2 holds no +R.
  expectRow(settled, "C1", R, OPEN);
  expectRow(settled, "B", R, OPEN);
}
test(
  "test_oracle_settled_overlap_validates_cover_and_enables_base_change",
  test_oracle_settled_overlap_validates_cover_and_enables_base_change,
);

function test_oracle_cover_closure_composes_covers(): void {
  // {C1, C2} ▷ B is valid; {D1, D2} ▷ C1 is unverified, because E ⊑ C1 has an unknown overlap
  // with D1 and D2. Transitivity gives {D1, D2, C2} ▷ B. A collision on E obstructs C1 and B for
  // P but not D1, D2 or C2, so the composed cover glues their Live +P into a record on B, while
  // gluing in two steps would need a Live +P on C1.
  const bs = twoCellCover();
  bs.defineBoundary("D1", { parents: ["C1"] });
  bs.defineBoundary("D2", { parents: ["C1"] });
  bs.declareDisjoint("D1", "D2");
  bs.defineBoundary("E", { parents: ["C1"] });
  bs.registerCover("B", ["C1", "C2"], "outer");
  bs.registerCover("C1", ["D1", "D2"], "inner");
  const m = evaluatePi({
    boundaries: bs,
    observations: [
      { boundary: "D1", polarity: "+", item: P },
      { boundary: "D2", polarity: "+", item: P },
      { boundary: "C2", polarity: "+", item: P },
      { boundary: "E", polarity: "+", item: P },
      { boundary: "E", polarity: "-", item: P },
    ],
  });

  assert.deepEqual(m.coverObligations, [
    { id: "inner", target: "C1", cells: ["D1", "D2"], validity: "unverified", subBoundaries: ["E"] },
  ]);
  assert.deepEqual(coversOf(m, "B"), ["B", "C1, C2", "C2, D1, D2"]);
  assert.deepEqual(coversOf(m, "C1"), ["C1", "D1, D2"]);
  // The base change of the inner cover to E is blocked by its unknown overlaps.
  assert.deepEqual(coversOf(m, "E"), ["E"]);

  expectRow(m, "E", P, { rec: ["true", "true"], coll: "true", obs: "true", status: "Collision", rev: true });
  for (const b of ["D1", "D2", "C2"]) {
    expectRow(m, b, P, GROUNDED_LIVE);
  }
  const gluedButObstructed: Expected = {
    rec: ["true", "false"],
    live: ["false", "false"],
    coll: "false",
    obs: "true",
    status: "Grounded",
    authority: ["Quarantined", null],
    rev: false,
  };
  // C1 glues D1 and D2 but is obstructed by E.
  expectRow(m, "C1", P, gluedButObstructed);
  // B takes its record from {D1, D2, C2} ▷ B alone, and is obstructed by E as well.
  expectRow(m, "B", P, gluedButObstructed);
  expectRow(m, TOP_BOUNDARY, P, { ...OPEN, obs: "true" });
  assert.deepEqual(revisionKeys(m), [`E ${itemKey(P)}`]);
  // E's -P meets the +P of D1 and of D2 across unknown overlaps (A29).
  assert.deepEqual(overlapKeys(m), [`D1 E ${itemKey(P)}`, `D2 E ${itemKey(P)}`]);
}
test("test_oracle_cover_closure_composes_covers", test_oracle_cover_closure_composes_covers);

function test_oracle_derived_empty_cover_is_an_error(): void {
  // {C1, C2} ▷ B is unverified (X ⊑ B is disjoint from C2 and of unknown overlap with C1) and
  // {D1} ▷ C1 is valid. Transitivity gives {D1, C2} ▷ B, whose base change to X is ∅ ▷ X, since
  // X is declared disjoint from D1 and C2: the closure breaks Non-Vacuity (A37).
  const system = (withInner: boolean): BoundarySystem => {
    const bs = twoCellCover();
    bs.defineBoundary("D1", { parents: ["C1"] });
    bs.defineBoundary("X", { parents: ["B"] });
    bs.declareDisjoint("X", "C2");
    bs.declareDisjoint("X", "D1");
    bs.registerCover("B", ["C1", "C2"], "cover-B");
    if (withInner) {
      bs.registerCover("C1", ["D1"], "cover-C1");
    }
    return bs;
  };
  assert.throws(
    () => evaluatePi({ boundaries: system(true), observations: [] }),
    /the base change of \{C2, D1\} ▷ B to X derives ∅ ▷ X, which Axiom 5 \(Non-Vacuity\) of item 5 forbids/,
  );

  // Without {D1} ▷ C1 nothing is derived from the unverified cover at X.
  const m = evaluatePi({ boundaries: system(false), observations: [] });
  assert.deepEqual(m.coverObligations, [
    { id: "cover-B", target: "B", cells: ["C1", "C2"], validity: "unverified", subBoundaries: ["X"] },
  ]);
  assert.deepEqual(coversOf(m, "X"), ["X"]);
}
test("test_oracle_derived_empty_cover_is_an_error", test_oracle_derived_empty_cover_is_an_error);

function test_oracle_cover_needs_an_ambiguous_meet_only_where_it_decides(): void {
  // A35. M1 and M2 are two maximal common sub-boundaries of B3 and C1, so their meet is
  // ambiguous.
  const ambiguous = (): BoundarySystem => {
    const bs = twoCellCover();
    bs.defineBoundary("B3", { parents: ["B"] });
    bs.defineBoundary("M1", { parents: ["B3", "C1"] });
    bs.defineBoundary("M2", { parents: ["B3", "C1"] });
    bs.registerCover("B", ["C1", "C2"], "cover-B");
    return bs;
  };

  // B3 is disjoint from C2, so whether it leaves the cover unsettled turns on its meet with C1.
  const undecided = ambiguous();
  undecided.declareDisjoint("B3", "C2");
  assert.throws(
    () => evaluatePi({ boundaries: undecided, observations: [] }),
    /judging the cover "cover-B" \(item 5\) needs the meet of "B3" and "C1", which is ambiguous/,
  );

  // A sub-boundary that refutes the cover makes it invalid whatever B3 is: no error. The
  // obligation of an invalid cover names only the refuting B4, not the unsettled B5 (A34).
  const refuted = ambiguous();
  refuted.declareDisjoint("B3", "C2");
  refuted.defineBoundary("B4", { parents: ["B"] });
  refuted.declareDisjoint("B4", "C1");
  refuted.declareDisjoint("B4", "C2");
  refuted.defineBoundary("B5", { parents: ["B"] });
  const invalid = evaluatePi({ boundaries: refuted, observations: [] });
  assert.deepEqual(invalid.coverObligations, [
    { id: "cover-B", target: "B", cells: ["C1", "C2"], validity: "invalid", subBoundaries: ["B4"] },
  ]);

  // B3 known to overlap C2 (through N) is no witness, so the cover is valid; but its base change
  // to B3 needs the ambiguous meet of C1 and B3.
  const baseChange = ambiguous();
  baseChange.defineBoundary("N", { parents: ["B3", "C2"] });
  assert.throws(
    () => evaluatePi({ boundaries: baseChange, observations: [] }),
    /the base change of \{C1, C2\} ▷ B to B3 \(item 5, Axiom 3\) needs the meet of "C1" and "B3", which is ambiguous/,
  );

  // Registering the meet settles it: the cover is valid, with the base change {M} ▷ B3.
  const resolved = ambiguous();
  resolved.declareDisjoint("B3", "C2");
  resolved.defineBoundary("M", { parents: ["B3", "C1"] });
  resolved.defineMeet("B3", "C1", "M");
  const m = evaluatePi({ boundaries: resolved, observations: [] });
  assert.deepEqual(m.coverObligations, []);
  assert.deepEqual(coversOf(m, "B3"), ["B3", "M"]);
}
test(
  "test_oracle_cover_needs_an_ambiguous_meet_only_where_it_decides",
  test_oracle_cover_needs_an_ambiguous_meet_only_where_it_decides,
);

function test_oracle_withdrawn_constraints_keep_their_items_tracked(): void {
  // A38. A withdrawn incompatibility or collapse is left out of the state and its items are
  // passed as history items: they stay in U(Σ, Q), but the constraint no longer applies.
  const singleBoundary = (): BoundarySystem => {
    const system = new BoundarySystem();
    system.defineBoundary("B");
    return system;
  };
  const observations = [{ boundary: "B", polarity: "+" as const, item: A }];
  const collapsed = implies(X, bottom());

  const inForce = evaluatePi({
    boundaries: singleBoundary(),
    observations,
    incompatibilities: [{ boundary: "B", left: A, right: C }],
    collapses: [{ boundary: "B", item: X }],
  });
  expectRow(inForce, "B", C, EXCLUDED_LIVE);
  expectRow(inForce, "B", X, EXCLUDED_LIVE);
  expectRow(inForce, "B", collapsed, GROUNDED_LIVE);

  const withdrawn = evaluatePi({
    boundaries: singleBoundary(),
    observations,
    historyItems: [A, C, X, collapsed],
  });
  assert.deepEqual(withdrawn.universe.map(itemKey).sort(), inForce.universe.map(itemKey).sort());
  for (const b of [TOP_BOUNDARY, "B"]) {
    expectRow(withdrawn, b, C, OPEN);
    expectRow(withdrawn, b, X, OPEN);
    expectRow(withdrawn, b, collapsed, OPEN);
  }
  expectRow(withdrawn, "B", A, GROUNDED_LIVE);

  // Without the history items, the withdrawn constraints' items leave the universe.
  const forgotten = evaluatePi({ boundaries: singleBoundary(), observations });
  assert.throws(() => forgotten.at("B", C), /outside/);
  assert.throws(() => forgotten.at("B", collapsed), /outside/);

  // A cover is withdrawn from the boundary system by its identifier. It names no item, so the
  // universe is unchanged, but it no longer witnesses: B loses the glued +E.
  const bs = twoCellCover();
  bs.registerCover("B", ["C1", "C2"], "cover-B");
  const glued = [
    { boundary: "C1", polarity: "+" as const, item: E },
    { boundary: "C2", polarity: "+" as const, item: E },
  ];
  const withCover = evaluatePi({ boundaries: bs, observations: glued });
  expectRow(withCover, "B", E, GROUNDED_LIVE);
  assert.equal(bs.withdrawCover("cover-B"), true);
  const withoutCover = evaluatePi({ boundaries: bs, observations: glued });
  assert.deepEqual(withoutCover.universe, withCover.universe);
  assert.deepEqual(coversOf(withoutCover, "B"), ["B"]);
  expectRow(withoutCover, "B", E, OPEN);
  expectRow(withoutCover, "C1", E, GROUNDED_LIVE);
}
test(
  "test_oracle_withdrawn_constraints_keep_their_items_tracked",
  test_oracle_withdrawn_constraints_keep_their_items_tracked,
);
