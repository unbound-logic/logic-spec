import assert from "node:assert/strict";
import { test } from "node:test";
import { BOT_BOUNDARY, BoundarySystem, TOP_BOUNDARY } from "../src/boundary.ts";
import { InquiryEngine } from "../src/engine.ts";
import { atom, equiv, flip, forall } from "../src/syntax.ts";

function test_boundary_meet_semilattice_and_non_witnessing_bottom(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B_all");
  b.defineBoundary("B_1atm", { parents: ["B_all"] });
  b.defineBoundary("B_2atm", { parents: ["B_all"] });
  b.declareDisjoint("B_1atm", "B_2atm");

  assert.equal(b.refines("B_1atm", "B_all"), true);
  assert.equal(b.refines("B_all", TOP_BOUNDARY), true);
  assert.equal(b.refines(BOT_BOUNDARY, "B_1atm"), true);
  assert.equal(b.refines("B_all", "B_1atm"), false);

  assert.equal(b.meet("B_1atm", "B_all"), "B_1atm");
  assert.equal(b.meet("B_1atm", "B_2atm"), BOT_BOUNDARY);
  assert.equal(b.overlaps("B_1atm", "B_2atm"), false);
  assert.equal(b.overlaps("B_1atm", "B_all"), true);

  // Non-Witnessing Law: ⊥_B cannot supply any genuine positive Witness (+)
  const engine = new InquiryEngine(b);
  assert.throws(
    () => engine.observePositive(BOT_BOUNDARY, atom("Anything"), "bad_w"),
    /Non-Witnessing Law/,
  );
}

function test_finitary_grothendieck_covers_meet_stability_and_non_vacuity(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Z");
  b.defineBoundary("Pos", { parents: ["Z"] });
  b.defineBoundary("NonPos", { parents: ["Z"] });
  b.declareDisjoint("Pos", "NonPos");

  b.defineBoundary("Even", { parents: ["Z"] });
  b.defineBoundary("Odd", { parents: ["Z"] });
  b.declareDisjoint("Even", "Odd");

  b.defineBoundary("PosEven", { parents: ["Pos", "Even"] });
  b.defineBoundary("PosOdd", { parents: ["Pos", "Odd"] });
  b.declareDisjoint("PosEven", "PosOdd");

  b.registerCover("Z", ["Even", "Odd"]);

  // Axiom 1 (Refinement): cell outside target rejected
  assert.throws(() => b.registerCover("Pos", ["Odd"]), /Refinement violation/);

  // Axiom 5 (Non-Vacuity): empty cover on non-empty boundary rejected
  assert.throws(() => b.registerCover("Z", []), /Non-Vacuity violation/);
  assert.equal(b.isWitnessedCover("Z", []), false);
  assert.equal(b.isWitnessedCover(BOT_BOUNDARY, []), true);

  // Axiom 2 (Identity)
  assert.equal(b.isWitnessedCover("Z", ["Z"]), true);

  // Axiom 3 (Meet-Stability): {Even, Odd} ▷ Z pulls back along Pos ⊑ Z to {PosEven, PosOdd} ▷ Pos
  assert.equal(b.isWitnessedCover("Pos", ["PosEven", "PosOdd"]), true);

  // Axiom 4 (Transitivity): refine Even into [EvenZero, EvenNonZero] and verify composed cover of Z
  b.defineBoundary("EvenZero", { parents: ["Even"] });
  b.defineBoundary("EvenNonZero", { parents: ["Even"] });
  b.declareDisjoint("EvenZero", "EvenNonZero");
  b.registerCover("Even", ["EvenZero", "EvenNonZero"]);
  assert.equal(b.isWitnessedCover("Z", ["EvenZero", "EvenNonZero", "Odd"]), true);
}

function test_coreference_multi_granularity_and_anti_equivocation(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B_macro", {
    nativeRelations: ["SameWaterway", "Navigable"],
    handles: [
      { id: "river_t0", criterion: "I_macro(river)", kind: "contingent" },
      { id: "river_t1", criterion: "I_macro(river)", kind: "contingent" },
    ],
  });
  b.defineBoundary("B_micro", {
    parents: ["B_macro"],
    nativeRelations: ["IdenticalMolecules"],
  });

  const engine = new InquiryEngine(b);
  const nav0 = atom("Navigable", [{ role: "entity", handle: "river_t0" }]);
  const nav1 = atom("Navigable", [{ role: "entity", handle: "river_t1" }]);
  const mol0 = atom("IdenticalMolecules", [{ role: "sample", handle: "river_t0" }]);
  const mol1 = atom("IdenticalMolecules", [{ role: "sample", handle: "river_t1" }]);

  engine.observePositive("B_macro", equiv("B_macro", "river_t0", "river_t1"), "w_eq", {
    handle: "river_t0",
    criterion: "I_macro(river)",
  });
  engine.observePositive("B_macro", nav0, "w_nav");
  engine.observePositive("B_micro", mol0, "w_mol0");
  engine.observeNegative("B_micro", mol1, "w_mol1");

  const snap = engine.evaluate([nav1, equiv("B_micro", "river_t0", "river_t1")]);
  // Native relation Navigable transfers via ≈_{B_macro}
  assert.equal(snap.statusOf("B_macro", nav1), "Grounded");
  assert.equal(snap.isLive("B_macro", "+", nav1), true);
  // Multi-granularity isolation: ≈_{B_macro} does not force IdenticalMolecules in B_micro
  assert.equal(snap.statusOf("B_micro", mol0), "Grounded");
  assert.equal(snap.statusOf("B_micro", mol1), "Excluded");
  assert.equal(snap.isCollisionFree(), true);

  // Anti-equivocation guard (worked-examples §2 Case 2C): bird_99 fails I_Swan
  b.defineBoundary("Swan", {
    nativeRelations: ["White", "Habitat"],
    handles: [{ id: "swan_402", criterion: "I_Swan(cygnus)", kind: "contingent" }],
  });
  const whiteBird99 = atom("White", [{ role: "subject", handle: "bird_99" }]);
  assert.throws(
    () =>
      engine.observeNegative("Swan", whiteBird99, "obs_wed", {
        handle: "bird_99",
        criterion: "I_Swan(cygnus)",
      }),
    /Anti-Equivocation violation/,
  );
}

function test_inquiry_updates_retract_non_commutativity_and_m1_m2(): void {
  // Part A: Pure Cancellation Retract returns to Open without fabricating opposite polarity
  const b0 = new BoundarySystem();
  b0.defineBoundary("B");
  const e0 = new InquiryEngine(b0);
  const planet = atom("Exists", [{ role: "body", handle: "planet_x" }]);
  e0.observeNegative("B", planet, "dust_artifact");
  assert.equal(e0.evaluate().statusOf("B", planet), "Excluded");
  assert.equal(e0.retract("dust_artifact"), true);
  assert.equal(e0.evaluate().statusOf("B", planet), "Open");
  assert.equal(e0.transitionLog.length, 2);
  assert.match(e0.transitionLog[0] ?? "", /Observe-/);
  assert.match(e0.transitionLog[1] ?? "", /Retract/);

  // MT-6 vertical non-commutativity: Observe+ ; Retract !== Retract ; Observe+
  const eSeq1 = new InquiryEngine(b0);
  eSeq1.observePositive("B", planet, "w_p");
  assert.equal(eSeq1.retract("w_p"), true);
  assert.equal(eSeq1.evaluate().statusOf("B", planet), "Open");

  const eSeq2 = new InquiryEngine(b0);
  assert.equal(eSeq2.retract("w_p"), false);
  eSeq2.observePositive("B", planet, "w_p");
  assert.equal(eSeq2.evaluate().statusOf("B", planet), "Grounded");

  // MT-6 Quarantine Reinstatement: retracting one colliding side restores Live to survivor
  const eRein = new InquiryEngine(b0);
  eRein.observePositive("B", planet, "w_pos");
  eRein.observeNegative("B", planet, "w_neg");
  const snapColl = eRein.evaluate();
  assert.equal(snapColl.statusOf("B", planet), "Collision");
  assert.equal(snapColl.isLive("B", "+", planet), false);
  assert.equal(eRein.retract("w_neg"), true);
  const snapRein = eRein.evaluate();
  assert.equal(snapRein.statusOf("B", planet), "Grounded");
  assert.equal(snapRein.isLive("B", "+", planet), true);

  // Part B: worked-examples §2 Case 2A — ℝ \ {0} passes M1 + M2
  const bMath = new BoundarySystem();
  bMath.defineBoundary("R", {
    nativeRelations: ["Invertible", "AddId"],
    handles: [
      { id: "0", criterion: "I_R(add_id)", kind: "structural" },
      { id: "2", criterion: "I_R(2)", kind: "structural" },
    ],
  });
  bMath.defineBoundary("R_star", {
    parents: ["R"],
    handleFilter: (h) => h.id !== "0",
  });
  const eMath = new InquiryEngine(bMath);
  const invX = atom("Invertible", [{ role: "el", handle: "x" }]);
  const genR = forall("x", "R", invX);
  eMath.observeNegative(
    "R",
    atom("Invertible", [{ role: "el", handle: "0" }]),
    "zero_no_inv",
  );
  const resR = eMath.refineBoundary({
    fromBoundary: "R",
    toBoundary: "R_star",
    originalUniversal: genR,
    targetRelation: "Invertible",
    criterionItem: flip(atom("AddId", [{ role: "el", handle: "x" }])),
  });
  assert.equal(resR.ok, true);
  assert.equal(eMath.evaluate([genR]).statusOf("R", genR), "Excluded");

  // Part C: worked-examples §2 Case 2B — Swan #402 M1 rejections and admissible M1+M2 split
  const bBio = new BoundarySystem();
  bBio.defineBoundary("Swan", {
    nativeRelations: ["White", "Habitat"],
    handles: [
      { id: "swan_402", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "Australia", criterion: "I_Region(AU)", kind: "structural" },
    ],
  });
  bBio.defineBoundary("Swan_NonAU", {
    parents: ["Swan"],
    handleFilter: (h) => h.id !== "swan_402",
  });
  const eBio = new InquiryEngine(bBio);
  const whiteX = atom("White", [{ role: "subject", handle: "x" }]);
  const genSwan = forall("x", "Swan", whiteX);
  eBio.observePositive("Swan", genSwan, "w_gen_swan");
  eBio.observeNegative(
    "Swan",
    atom("White", [{ role: "subject", handle: "swan_402" }]),
    "obs_tue",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
  assert.equal(eBio.evaluate().statusOf("Swan", genSwan), "Collision");

  // Attempt 1: δ₁(x) := White(x) -> refused M1(i) circular
  const att1 = eBio.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: whiteX,
  });
  assert.equal(att1.ok, false);
  if (!att1.ok) {
    assert.equal(att1.violation, "M1-circular");
  }

  // Attempt 2: δ₂(x) := ~(x ≈_Swan swan_402) -> refused M1(ii) contingent handle excision
  const att2 = eBio.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: flip(equiv("Swan", "x", "swan_402")),
  });
  assert.equal(att2.ok, false);
  if (!att2.ok) {
    assert.equal(att2.violation, "M1-contingent-excision");
  }

  // Attempt 3: δ₃(x) := ~Habitat(x, Australia) -> admitted; M2 preserves (Swan, Gen_Swan) Excluded after retracting overbroad w_gen_swan
  eBio.retract("w_gen_swan");
  const att3 = eBio.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: flip(
      atom("Habitat", [
        { role: "subject", handle: "x" },
        { role: "region", handle: "Australia" },
      ]),
    ),
  });
  assert.equal(att3.ok, true);
  assert.equal(eBio.evaluate().statusOf("Swan", genSwan), "Excluded");
}

test("boundary meet-semilattice and non-witnessing bottom", test_boundary_meet_semilattice_and_non_witnessing_bottom);
test("finitary Grothendieck covers meet-stability and non-vacuity", test_finitary_grothendieck_covers_meet_stability_and_non_vacuity);
test("co-reference multi-granularity isolation and anti-equivocation", test_coreference_multi_granularity_and_anti_equivocation);
test("inquiry updates retract non-commutativity and M1/M2", test_inquiry_updates_retract_non_commutativity_and_m1_m2);
