/**
 * Hand-computed cases for the clean-room Π(Σ) oracle in test/oracle/pi-sigma.ts
 * (spec/core.md §5 item 14, as amended in main commit 7b36043). Every expectation is derived
 * by hand from item 14's program, rule table and Reporting section (G4b); readings follow
 * test/oracle/AMBIGUITIES.md.
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
