import assert from "node:assert/strict";
import { test } from "node:test";
import { BOT_BOUNDARY, BoundarySystem, TOP_BOUNDARY } from "../src/boundary.ts";
import { InquiryEngine } from "../src/engine.ts";
import { and, atom, bottom, equiv, exists, flip, forall, implies, itemKey, or } from "../src/syntax.ts";

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

function test_registered_meet_is_the_greatest_lower_bound(): void {
  const h = (id: string) => ({ id, criterion: `I(${id})`, kind: "structural" as const });

  // A boundary defined below both members of a pair lies below their registered meet, so Bpp
  // cannot be declared disjoint from M, and the base change {M} ▷ Bp of the valid cover
  // {C1, C2} ▷ B stays valid (clean-room oracle reading A39).
  const b = new BoundarySystem();
  b.defineBoundary("B");
  b.defineBoundary("C1", { parents: ["B"] });
  b.defineBoundary("C2", { parents: ["B"] });
  b.declareDisjoint("C1", "C2");
  b.defineBoundary("Bp", { parents: ["B"] });
  b.declareDisjoint("Bp", "C2");
  b.defineBoundary("M", { parents: ["Bp", "C1"] });
  b.defineMeet("Bp", "C1", "M");
  b.defineBoundary("Bpp", { parents: ["Bp"] });
  b.defineBoundary("N", { parents: ["Bpp", "C1"] });
  assert.equal(b.refines("N", "M"), true);
  assert.deepEqual(b.meetStatus("Bpp", "M"), { kind: "overlap", meet: "N" });
  assert.throws(() => b.declareDisjoint("Bpp", "M"), /common non-empty sub-boundaries/);
  const cov = b.registerCover("B", ["C1", "C2"]);
  assert.deepEqual(b.coverValidity(cov), { kind: "valid" });
  assert.equal(b.isWitnessedCover("Bp", ["M"]), true);
  assert.deepEqual(b.judgeCover("Bp", ["M"]), { kind: "valid" });

  // Registering a meet settles an ambiguity: the maximal common sub-boundaries lie below it.
  const a = new BoundarySystem();
  a.defineBoundary("Lab");
  a.defineBoundary("Field");
  a.defineBoundary("M1", { parents: ["Lab", "Field"] });
  a.defineBoundary("M2", { parents: ["Lab", "Field"] });
  assert.throws(() => a.meetStatus("Lab", "Field"), /Ambiguous meet/);
  a.defineBoundary("M", { parents: ["Lab", "Field"] });
  a.defineMeet("Lab", "Field", "M");
  assert.deepEqual(a.meetStatus("Lab", "Field"), { kind: "overlap", meet: "M" });
  assert.equal(a.refines("M1", "M"), true);
  assert.equal(a.refines("M2", "M"), true);
  assert.deepEqual(a.meetStatus("M1", "M2"), { kind: "unknown" });

  // Inferred refinements obey domain monotonicity (item 6): a meet whose domain misses a handle of
  // a common sub-boundary is refused, and a later boundary below both members takes its default
  // handles from the meet as well, or is refused with a handle outside it.
  const d = new BoundarySystem();
  d.defineBoundary("P", { handles: [h("x"), h("y")] });
  d.defineBoundary("Q", { handles: [h("x"), h("y")] });
  d.defineBoundary("Wide", { parents: ["P", "Q"], handles: [h("x"), h("y")] });
  d.defineBoundary("Narrow", { parents: ["P", "Q"], handles: [h("x")] });
  assert.throws(() => d.defineMeet("P", "Q", "Narrow"), /domain monotonicity/);
  assert.equal(d.refines("Wide", "Narrow"), false);
  const e = new BoundarySystem();
  e.defineBoundary("P", { handles: [h("x"), h("y")] });
  e.defineBoundary("Q", { handles: [h("x"), h("y")] });
  e.defineBoundary("M", { parents: ["P", "Q"], handles: [h("x")] });
  e.defineMeet("P", "Q", "M");
  e.defineBoundary("R", { parents: ["P", "Q"] });
  assert.deepEqual(e.handlesOf("R").map((x) => x.id), ["x"]);
  assert.throws(
    () => e.defineBoundary("S", { parents: ["P", "Q"], handles: [h("y")] }),
    /Domain monotonicity violation: handle "y" of "S" is not in Dom\("M"\)/,
  );
  // A meet that would make two distinct boundaries refine each other is refused: for a comparable
  // pair the meet is the smaller one, and a common sub-boundary above the meet would equal it.
  const c = new BoundarySystem();
  c.defineBoundary("Big");
  c.defineBoundary("Small", { parents: ["Big"] });
  c.defineBoundary("Tiny", { parents: ["Small"] });
  assert.throws(() => c.defineMeet("Big", "Small", "Tiny"), /refine each other/);
  c.defineBoundary("Other");
  c.defineBoundary("Shared", { parents: ["Big", "Other"] });
  c.defineBoundary("Inner", { parents: ["Shared"] });
  assert.throws(() => c.defineMeet("Big", "Other", "Inner"), /refine each other/);
  assert.equal(c.refines("Shared", "Inner"), false);
  // A boundary below a meet and below a boundary declared disjoint from it is refused.
  e.defineBoundary("Z", { handles: [h("x")] });
  e.declareDisjoint("M", "Z");
  assert.throws(
    () => e.defineBoundary("W", { parents: ["P", "Q", "Z"], handles: [h("x")] }),
    /below disjoint boundaries "M" and "Z"/,
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

  // Axiom 3 across an unknown overlap: Odd may hold part of X, so {Even, Odd} ▷ Z has no base change to X.
  const u = new BoundarySystem();
  u.defineBoundary("Z");
  u.defineBoundary("Even", { parents: ["Z"] });
  u.defineBoundary("Odd", { parents: ["Z"] });
  u.declareDisjoint("Even", "Odd");
  u.defineBoundary("X", { parents: ["Z"] });
  u.defineBoundary("EvenX", { parents: ["Even", "X"] });
  u.registerCover("Z", ["Even", "Odd"]);
  assert.deepEqual(u.meetStatus("Odd", "X"), { kind: "unknown" });
  assert.equal(u.isWitnessedCover("X", ["EvenX"]), false);
  // Declaring Odd and X disjoint settles the overlap, and the base change {EvenX} ▷ X follows.
  u.declareDisjoint("Odd", "X");
  assert.equal(u.isWitnessedCover("X", ["EvenX"]), true);
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
  assert.equal(snap.localStatus("B_macro", nav1), "Grounded");
  assert.equal(snap.isLive("B_macro", "+", nav1), true);
  // Multi-granularity isolation: ≈_{B_macro} does not force IdenticalMolecules in B_micro
  assert.equal(snap.localStatus("B_micro", mol0), "Grounded");
  assert.equal(snap.localStatus("B_micro", mol1), "Excluded");
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
  assert.equal(e0.evaluate().localStatus("B", planet), "Excluded");
  assert.equal(e0.retract("dust_artifact"), true);
  assert.equal(e0.evaluate().localStatus("B", planet), "Open");
  assert.equal(e0.transitionLog.length, 2);
  assert.match(e0.transitionLog[0] ?? "", /Observe-/);
  assert.match(e0.transitionLog[1] ?? "", /Retract/);

  // MT-6 vertical non-commutativity: Observe+ ; Retract !== Retract ; Observe+
  const eSeq1 = new InquiryEngine(b0);
  eSeq1.observePositive("B", planet, "w_p");
  assert.equal(eSeq1.retract("w_p"), true);
  assert.equal(eSeq1.evaluate().localStatus("B", planet), "Open");

  const eSeq2 = new InquiryEngine(b0);
  assert.equal(eSeq2.retract("w_p"), false);
  eSeq2.observePositive("B", planet, "w_p");
  assert.equal(eSeq2.evaluate().localStatus("B", planet), "Grounded");

  // MT-6 Quarantine Reinstatement: retracting one colliding side restores Live to survivor
  const eRein = new InquiryEngine(b0);
  eRein.observePositive("B", planet, "w_pos");
  eRein.observeNegative("B", planet, "w_neg");
  const snapColl = eRein.evaluate();
  assert.equal(snapColl.localStatus("B", planet), "Collision");
  assert.equal(snapColl.isLive("B", "+", planet), false);
  assert.equal(eRein.retract("w_neg"), true);
  const snapRein = eRein.evaluate();
  assert.equal(snapRein.localStatus("B", planet), "Grounded");
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
  // Separating evidence for M1's domain binding: the excised handle 0 is the additive identity.
  eMath.observePositive("R", atom("AddId", [{ role: "el", handle: "0" }]), "zero_is_add_id");
  const resR = eMath.refineBoundary({
    fromBoundary: "R",
    toBoundary: "R_star",
    originalUniversal: genR,
    targetRelation: "Invertible",
    criterionItem: flip(atom("AddId", [{ role: "el", handle: "x" }])),
  });
  assert.equal(resR.ok, true);
  assert.equal(eMath.evaluate([genR]).localStatus("R", genR), "Excluded");

  // Part C: worked-examples §2 Case 2B — Swan #402 M1 rejections and admissible M1+M2 split
  const bBio = new BoundarySystem();
  bBio.defineBoundary("Swan", {
    nativeRelations: ["White", "Habitat"],
    handles: [
      { id: "swan_402", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "swan_101", criterion: "I_Swan(cygnus)", kind: "contingent" },
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
  eBio.observeNegative(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_101" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_eu_habitat",
    { handle: "swan_101", criterion: "I_Swan(cygnus)" },
  );
  assert.equal(eBio.evaluate().localStatus("Swan", genSwan), "Collision");

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

  // Attempt 3: δ₃(x) := ~Habitat(x, Australia) -> admitted via independent witness swan_101; M2 preserves (Swan, Gen_Swan) Excluded
  eBio.retract("w_gen_swan");
  // Separating evidence for M1's domain binding: the excised swan_402 lives in Australia.
  eBio.observePositive(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_402" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_402_au_habitat",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
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
  assert.equal(eBio.evaluate().localStatus("Swan", genSwan), "Excluded");
}

function test_m1_iii_excess_content_blocks_disguised_proxies_and_preserves_structural_singularities(): void {
  const bProxy = new BoundarySystem();
  bProxy.defineBoundary("Swan", {
    nativeRelations: ["White", "Habitat", "FoundInLake7", "TaggedOnTuesday"],
    handles: [
      { id: "swan_402", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "swan_101", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "Australia", criterion: "I_Region(AU)", kind: "structural" },
    ],
  });
  bProxy.defineBoundary("Swan_NonAU", {
    parents: ["Swan"],
    handleFilter: (h) => h.id !== "swan_402",
  });
  bProxy.defineBoundary("Swan_Empty", {
    parents: ["Swan"],
    handleFilter: () => false,
  });

  const eProxy = new InquiryEngine(bProxy);
  const whiteX = atom("White", [{ role: "subject", handle: "x" }]);
  const genSwan = forall("x", "Swan", whiteX);
  eProxy.observeNegative(
    "Swan",
    atom("White", [{ role: "subject", handle: "swan_402" }]),
    "obs_tue",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
  eProxy.observePositive(
    "Swan",
    atom("FoundInLake7", [{ role: "subject", handle: "swan_402" }]),
    "obs_lake7",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
  eProxy.observePositive(
    "Swan",
    atom("TaggedOnTuesday", [{ role: "subject", handle: "swan_402" }]),
    "obs_tag_tue",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );

  // Attempt 2b: disguised contingent proxy ~(FoundInLake7(x) ∧ TaggedOnTuesday(x)) -> refused M1(iii)
  const proxyCrit = flip(
    and(
      atom("FoundInLake7", [{ role: "subject", handle: "x" }]),
      atom("TaggedOnTuesday", [{ role: "subject", handle: "x" }]),
    ),
  );
  const resProxy = eProxy.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: proxyCrit,
  });
  assert.equal(resProxy.ok, false);
  if (!resProxy.ok) {
    assert.equal(resProxy.violation, "M1-unwitnessed-proxy");
  }

  // Independent negative observation on swan_101 for Habitat(swan_101, Australia)
  const habX = flip(
    atom("Habitat", [
      { role: "subject", handle: "x" },
      { role: "region", handle: "Australia" },
    ]),
  );
  eProxy.observeNegative(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_101" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_eu_habitat",
    { handle: "swan_101", criterion: "I_Swan(cygnus)" },
  );

  // Vacuous excision removing all surviving handles -> refused M1(iii)
  const resEmpty = eProxy.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_Empty",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: habX,
  });
  assert.equal(resEmpty.ok, false);
  if (!resEmpty.ok) {
    assert.equal(resEmpty.violation, "M1-unwitnessed-proxy");
  }

  // Collided/Quarantined witness on swan_101 cannot satisfy M1(iii)
  eProxy.observePositive(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_101" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_au_conflict",
    { handle: "swan_101", criterion: "I_Swan(cygnus)" },
  );
  const resCollided = eProxy.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: habX,
  });
  assert.equal(resCollided.ok, false);
  if (!resCollided.ok) {
    assert.equal(resCollided.violation, "M1-unwitnessed-proxy");
  }

  // Retracting conflicting observation restores Live witness on swan_101 -> M1(iii) admits + M2 preserves Excluded
  assert.equal(eProxy.retract("obs_au_conflict"), true);
  // Separating evidence for M1's domain binding: the excised swan_402 lives in Australia.
  eProxy.observePositive(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_402" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_402_au_habitat",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
  const resAdmitted = eProxy.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: habX,
  });
  assert.equal(resAdmitted.ok, true);
  assert.equal(eProxy.evaluate([genSwan]).localStatus("Swan", genSwan), "Excluded");

  // Structural singularity exemption: ℝ \ {0} removes only structural handle "0", needing no extra empirical witness
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
  eMath.observeNegative("R", atom("Invertible", [{ role: "el", handle: "0" }]), "zero_no_inv");
  eMath.observePositive("R", atom("AddId", [{ role: "el", handle: "0" }]), "zero_is_add_id");
  const resMath = eMath.refineBoundary({
    fromBoundary: "R",
    toBoundary: "R_star",
    originalUniversal: genR,
    targetRelation: "Invertible",
    criterionItem: flip(atom("AddId", [{ role: "el", handle: "x" }])),
  });
  assert.equal(resMath.ok, true);

  // Reject surviving handle whose sole witness is Live -δ(u) (contradicts B' = B ⊓ [δ])
  const eOnlyNeg = new InquiryEngine(bProxy);
  eOnlyNeg.observeNegative(
    "Swan",
    atom("White", [{ role: "subject", handle: "swan_402" }]),
    "obs_tue",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
  eOnlyNeg.observePositive(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_101" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_au_only",
    { handle: "swan_101", criterion: "I_Swan(cygnus)" },
  );
  const resNegWitness = eOnlyNeg.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: habX,
  });
  assert.equal(resNegWitness.ok, false);
  if (!resNegWitness.ok) {
    assert.equal(resNegWitness.violation, "M1-unwitnessed-proxy");
  }

  // Reject keeping a surviving handle with Live -δ(v) even when another handle has Live +δ(u)
  const bTwo = new BoundarySystem();
  bTwo.defineBoundary("Swan", {
    nativeRelations: ["White", "Habitat"],
    handles: [
      { id: "swan_402", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "swan_101", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "swan_102", criterion: "I_Swan(cygnus)", kind: "contingent" },
      { id: "Australia", criterion: "I_Region(AU)", kind: "structural" },
    ],
  });
  bTwo.defineBoundary("Swan_NonAU", {
    parents: ["Swan"],
    handleFilter: (h) => h.id !== "swan_402",
  });
  const eTwo = new InquiryEngine(bTwo);
  eTwo.observeNegative(
    "Swan",
    atom("White", [{ role: "subject", handle: "swan_402" }]),
    "obs_tue",
    { handle: "swan_402", criterion: "I_Swan(cygnus)" },
  );
  eTwo.observeNegative(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_101" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_eu_101",
    { handle: "swan_101", criterion: "I_Swan(cygnus)" },
  );
  eTwo.observePositive(
    "Swan",
    atom("Habitat", [
      { role: "subject", handle: "swan_102" },
      { role: "region", handle: "Australia" },
    ]),
    "obs_au_102",
    { handle: "swan_102", criterion: "I_Swan(cygnus)" },
  );
  const resInconsistentSurvivor = eTwo.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_NonAU",
    originalUniversal: genSwan,
    targetRelation: "White",
    criterionItem: habX,
  });
  assert.equal(resInconsistentSurvivor.ok, false);
  if (!resInconsistentSurvivor.ok) {
    assert.equal(resInconsistentSurvivor.violation, "M1-unwitnessed-proxy");
  }
}

function test_core_engine_congruence_forall_elim_domain_constraint_and_semilattice_consistency(): void {
  // 1. Semilattice consistency checks between defineMeet / declareDisjoint / defineBoundary
  const bSem = new BoundarySystem();
  bSem.defineBoundary("A");
  bSem.defineBoundary("B");
  bSem.declareDisjoint("A", "B");
  assert.throws(() => bSem.defineBoundary("Joint", { parents: ["A", "B"] }), /disjoint/i);
  assert.throws(() => bSem.defineMeet("A", "B", "A"), /refine|disjoint/i);

  const bSem2 = new BoundarySystem();
  bSem2.defineBoundary("P");
  bSem2.defineBoundary("Q");
  bSem2.defineBoundary("PQ", { parents: ["P", "Q"] });
  assert.throws(() => bSem2.declareDisjoint("P", "Q"), /common|meet|disjoint|refine/i);
  assert.throws(() => bSem2.defineMeet("P", "Q", BOT_BOUNDARY), /common|meet|disjoint|refine/i);
  assert.throws(() => bSem2.defineMeet("P", "PQ", BOT_BOUNDARY), /refine|disjoint/i);

  const bSem3 = new BoundarySystem();
  bSem3.defineBoundary("X");
  bSem3.defineBoundary("Y");
  bSem3.defineBoundary("XY", { parents: ["X", "Y"] });
  bSem3.defineMeet("X", "Y", "XY");
  assert.throws(() => bSem3.declareDisjoint("X", "Y"), /meet|common|disjoint/i);

  const bSem4 = new BoundarySystem();
  bSem4.defineBoundary("U");
  bSem4.defineBoundary("V");
  bSem4.defineMeet("U", "V", BOT_BOUNDARY);
  assert.throws(() => bSem4.defineBoundary("UV", { parents: ["U", "V"] }), /disjoint/i);
  bSem4.defineBoundary("U1", { parents: ["U"] });
  bSem4.defineBoundary("V1", { parents: ["V"] });
  assert.throws(() => bSem4.defineBoundary("U1V1", { parents: ["U1", "V1"] }), /disjoint/i);
  assert.equal(bSem4.meet("U1", "V1"), BOT_BOUNDARY);
  assert.equal(bSem4.overlaps("U1", "V1"), false);

  // 2. ≈_B reflexivity, symmetry, transitivity + engine-side ∀E + domainConstraint + Live-gated ∃I
  const b = new BoundarySystem();
  b.defineBoundary("D", {
    nativeRelations: ["P", "Q", "Delta"],
    handles: [
      { id: "t1", criterion: "I(t1)", kind: "structural" },
      { id: "t2", criterion: "I(t2)", kind: "structural" },
      { id: "t3", criterion: "I(t3)", kind: "structural" },
    ],
  });
  const e = new InquiryEngine(b);
  const p = (h: string) => atom("P", [{ role: "arg", handle: h }]);
  const q = (h: string) => atom("Q", [{ role: "arg", handle: h }]);
  const delta = (h: string) => atom("Delta", [{ role: "arg", handle: h }]);

  // ≈_B laws
  e.observePositive("D", equiv("D", "t1", "t2"), "w_12");
  e.observePositive("D", equiv("D", "t2", "t3"), "w_23");
  const snapEq = e.evaluate([equiv("D", "t1", "t1"), equiv("D", "t2", "t1"), equiv("D", "t1", "t3")]);
  assert.equal(snapEq.isLive("D", "+", equiv("D", "t1", "t1")), true);
  assert.equal(snapEq.isLive("D", "+", equiv("D", "t2", "t1")), true);
  assert.equal(snapEq.isLive("D", "+", equiv("D", "t1", "t3")), true);

  // Engine-side ∀E
  e.observePositive("D", forall("x", "D", p("x")), "w_all_p");
  const snapForallE = e.evaluate([p("t1"), p("t2"), p("t3")]);
  assert.equal(snapForallE.isLive("D", "+", p("t1")), true);
  assert.equal(snapForallE.isLive("D", "+", p("t2")), true);
  assert.equal(snapForallE.isLive("D", "+", p("t3")), true);

  // domainConstraint on ∀ and ∃
  const eDom = new InquiryEngine(b);
  eDom.observePositive("D", delta("t1"), "w_d1");
  eDom.observeNegative("D", delta("t2"), "w_nd2");
  eDom.observeNegative("D", delta("t3"), "w_nd3");
  eDom.observePositive("D", p("t1"), "w_p1");
  eDom.observeNegative("D", p("t2"), "w_np2");
  eDom.observePositive("D", q("t2"), "w_q2");
  eDom.observeNegative("D", q("t1"), "w_nq1");
  eDom.closeDomain("D");

  const constrainedAll = forall("x", "D", p("x"), delta("x"));
  const constrainedEx = exists("x", "D", q("x"), delta("x"));
  const snapDom = eDom.evaluate([constrainedAll, constrainedEx]);
  assert.equal(snapDom.localStatus("D", constrainedAll), "Grounded");
  assert.equal(snapDom.isLive("D", "+", constrainedAll), true);
  assert.equal(snapDom.allGrounds("D", "+", constrainedEx).length, 0);
  assert.equal(snapDom.localStatus("D", constrainedEx), "Excluded");
  assert.equal(snapDom.isLive("D", "-", constrainedEx), true);

  // Live-gated exists-intro: collided +P(t1) must NOT witness +∃(x : D) P(x)
  const eExLive = new InquiryEngine(b);
  const exP = exists("x", "D", p("x"));
  eExLive.observePositive("D", p("t1"), "w_p1");
  eExLive.observeNegative("D", p("t1"), "w_np1");
  eExLive.observeNegative("D", exP, "w_nex");
  const snapEx = eExLive.evaluate([exP]);
  assert.equal(snapEx.allGrounds("D", "+", exP).length, 0);
  assert.equal(snapEx.localStatus("D", exP), "Excluded");
  assert.equal(snapEx.isLive("D", "-", exP), true);
}

function test_domain_monotonicity_rejects_sub_boundary_handles(): void {
  const h = (id: string) => ({ id, criterion: `I(${id})`, kind: "structural" as const });
  const ids = (bs: BoundarySystem, boundary: string) => bs.handlesOf(boundary).map((x) => x.id).sort();
  const b = new BoundarySystem();
  b.defineBoundary("D", { handles: [h("a"), h("b"), h("c")] });

  // A sub-boundary may narrow its parent's domain but never add an individual the parent lacks.
  b.defineBoundary("D_ab", { parents: ["D"], handles: [h("a"), h("b")] });
  b.defineBoundary("D_bc", { parents: ["D"], handles: [h("b"), h("c")] });
  assert.deepEqual(ids(b, "D_ab"), ["a", "b"]);
  assert.throws(
    () => b.defineBoundary("D_bad", { parents: ["D_ab"], handles: [h("a"), h("c")] }),
    /Domain monotonicity violation: handle "c"/,
  );
  assert.throws(() => b.refines("D_bad", "D"), /Unknown boundary/);

  // With several parents the handles must lie in every parent.
  assert.throws(
    () => b.defineBoundary("D_joint_bad", { parents: ["D_ab", "D_bc"], handles: [h("a"), h("b")] }),
    /Domain monotonicity violation: handle "a" of "D_joint_bad" is not in Dom\("D_bc"\)/,
  );

  // Default handles: those common to every parent, then the handle filter.
  b.defineBoundary("D_joint", { parents: ["D_ab", "D_bc"] });
  assert.deepEqual(ids(b, "D_joint"), ["b"]);
  b.defineBoundary("D_inherit", { parents: ["D_ab"] });
  assert.deepEqual(ids(b, "D_inherit"), ["a", "b"]);
  b.defineBoundary("D_filtered", { parents: ["D_ab", "D_bc"], handleFilter: (x) => x.id !== "b" });
  assert.deepEqual(ids(b, "D_filtered"), []);

  // ⊤_B carries no handle registry and constrains nothing.
  b.defineBoundary("Free", { handles: [h("z")] });
  assert.deepEqual(ids(b, "Free"), ["z"]);

  // Disjoint parents are rejected before the monotonicity check.
  b.defineBoundary("X", { handles: [h("x")] });
  b.defineBoundary("Y", { handles: [h("y")] });
  b.declareDisjoint("X", "Y");
  assert.throws(() => b.defineBoundary("XY", { parents: ["X", "Y"], handles: [h("x")] }), /disjoint parents/);
}

function test_close_domain_gates_enumerative_quantifiers(): void {
  const h = (id: string) => ({ id, criterion: `I(${id})`, kind: "structural" as const });
  const b = new BoundarySystem();
  b.defineBoundary("D", { nativeRelations: ["P", "Q", "R"], handles: [h("t1"), h("t2")] });
  b.defineBoundary("D_sub", { parents: ["D"], handles: [h("t1")] });
  b.defineBoundary("Empty", { handles: [] });
  const p = (x: string) => atom("P", [{ role: "arg", handle: x }]);
  const q = (x: string) => atom("Q", [{ role: "arg", handle: x }]);
  const r = (x: string) => atom("R", [{ role: "arg", handle: x }]);
  const allP = forall("x", "D", p("x"));
  const exP = exists("x", "D", p("x"));

  const e = new InquiryEngine(b);
  e.observePositive("D", p("t1"), "w_p1");
  e.observePositive("D", p("t2"), "w_p2");

  // Unclosed domain: enumeration never grounds +∀; +∃ stays open-world (one witness suffices).
  const stageOpen = e.stage;
  let snap = e.evaluate([allP, exP]);
  assert.equal(snap.localStatus("D", allP), "Open");
  assert.equal(snap.localStatus("D", exP), "Grounded");
  assert.equal(e.isDomainClosed("D"), false);

  // CloseDomain(D) is a stage-archived transition that licenses enumerative +∀.
  e.closeDomain("D");
  assert.equal(e.stage, stageOpen + 1);
  assert.equal(e.transitionLog.at(-1), `Σ${e.stage}:CloseDomain(D)`);
  assert.equal(e.isDomainClosed("D"), true);
  snap = e.evaluate([allP]);
  assert.equal(snap.localStatus("D", allP), "Grounded");
  assert.equal(snap.isLive("D", "+", allP), true);
  assert.ok(
    snap
      .liveGrounds("D", "+", allP)
      .some((g) => g.provenance.kind === "derived" && g.provenance.baseLeaves.includes("@closure:D")),
  );
  assert.equal(e.evaluateAtStage(stageOpen, [allP]).localStatus("D", allP), "Open");

  // The closure belongs to D alone and does not pass to its sub-boundary D_sub.
  const allPSub = forall("x", "D_sub", p("x"));
  assert.equal(e.isDomainClosed("D_sub"), false);
  assert.equal(e.evaluate([allPSub]).localStatus("D_sub", allPSub), "Open");

  // -∃ by enumeration needs the closure as well; an exclusion record per handle suffices.
  e.observeNegative("D", q("t1"), "w_nq1");
  e.observeNegative("D", q("t2"), "w_nq2");
  const exQ = exists("x", "D", q("x"));
  const exQSub = exists("x", "D_sub", q("x"));
  snap = e.evaluate([exQ, exQSub]);
  assert.equal(snap.localStatus("D", exQ), "Excluded");
  assert.equal(snap.isLive("D", "-", exQ), true);
  assert.equal(snap.localStatus("D_sub", exQSub), "Open");

  // An empty D_δ: every handle carries Live -δ, so +∀ holds vacuously on the closed domain.
  e.observeNegative("D", r("t1"), "w_nr1");
  e.observeNegative("D", r("t2"), "w_nr2");
  const allQGivenR = forall("x", "D", q("x"), r("x"));
  snap = e.evaluate([allQGivenR]);
  assert.equal(snap.localStatus("D", allQGivenR), "Grounded");
  assert.equal(snap.isLive("D", "+", allQGivenR), true);

  // An empty Dom(D): Open while unclosed, vacuous +∀ and -∃ once closed (no admissible witness needed).
  const allEmpty = forall("x", "Empty", p("x"));
  const exEmpty = exists("x", "Empty", p("x"));
  snap = e.evaluate([allEmpty, exEmpty]);
  assert.equal(snap.localStatus("D", allEmpty), "Open");
  assert.equal(snap.localStatus("D", exEmpty), "Open");
  e.closeDomain("Empty");
  snap = e.evaluate([allEmpty, exEmpty]);
  assert.equal(snap.localStatus("D", allEmpty), "Grounded");
  assert.equal(snap.isLive("D", "+", allEmpty), true);
  assert.equal(snap.localStatus("D", exEmpty), "Excluded");
  assert.equal(snap.isLive("D", "-", exEmpty), true);

  // D ≠ ⊥_B: ⊥_B can never be closed, so a quantifier over it is never grounded by enumeration.
  assert.throws(() => e.closeDomain(BOT_BOUNDARY), /CloseDomain requires a boundary D ≠/);
  assert.throws(() => e.closeDomain("Nowhere"), /Unknown boundary/);
  const allBot = forall("x", BOT_BOUNDARY, p("x"));
  assert.equal(e.evaluate([allBot]).localStatus("D", allBot), "Open");
}

function test_m1_binding_rejects_criteria_not_shown_to_exclude_excised_handles(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Swan", {
    nativeRelations: ["White", "Feathered", "Habitat"],
    handles: [
      { id: "swan_402", criterion: "I_Swan", kind: "contingent" },
      { id: "swan_101", criterion: "I_Swan", kind: "contingent" },
    ],
  });
  b.defineBoundary("Swan_Rest", { parents: ["Swan"], handleFilter: (h) => h.id !== "swan_402" });
  const rel = (name: string, handle: string) => atom(name, [{ role: "subject", handle }]);
  const auth = (handle: string) => ({ handle, criterion: "I_Swan" });
  const gen = forall("x", "Swan", rel("White", "x"));
  const request = (criterionItem: ReturnType<typeof rel>) => ({
    fromBoundary: "Swan",
    toBoundary: "Swan_Rest",
    originalUniversal: gen,
    targetRelation: "White",
    criterionItem,
  });

  // A decorative criterion: the excised counterexample satisfies δ := Feathered(x).
  const e = new InquiryEngine(b);
  e.observeNegative("Swan", rel("White", "swan_402"), "obs_black", auth("swan_402"));
  e.observePositive("Swan", rel("Feathered", "swan_101"), "f101", auth("swan_101"));
  e.observePositive("Swan", rel("Feathered", "swan_402"), "f402", auth("swan_402"));
  const decorative = e.refineBoundary(request(rel("Feathered", "x")));
  assert.equal(decorative.ok, false);
  if (!decorative.ok) {
    assert.equal(decorative.violation, "M1-unbound-criterion");
  }

  // A criterion never tested against the excised handle (δ(swan_402) Open) is refused too ...
  const e2 = new InquiryEngine(b);
  e2.observeNegative("Swan", rel("White", "swan_402"), "obs_black", auth("swan_402"));
  e2.observePositive("Swan", rel("Habitat", "swan_101"), "h101", auth("swan_101"));
  const untested = e2.refineBoundary(request(rel("Habitat", "x")));
  assert.equal(untested.ok, false);
  if (!untested.ok) {
    assert.equal(untested.violation, "M1-unbound-criterion");
  }
  // ... and admitted once separating evidence shows that swan_402 fails δ.
  e2.observeNegative("Swan", rel("Habitat", "swan_402"), "h402", auth("swan_402"));
  assert.equal(e2.refineBoundary(request(rel("Habitat", "x"))).ok, true);

  // A kept handle whose δ is Live excluded breaks Dom(B') = {h ∈ Dom(B) : ¬Live -δ(h)}.
  const r = new BoundarySystem();
  r.defineBoundary("R", {
    nativeRelations: ["Invertible", "AddId"],
    handles: [
      { id: "0", criterion: "I_R(0)", kind: "structural" },
      { id: "2", criterion: "I_R(2)", kind: "structural" },
      { id: "3", criterion: "I_R(3)", kind: "structural" },
    ],
  });
  r.defineBoundary("R_star", { parents: ["R"], handleFilter: (h) => h.id !== "0" });
  const el = (name: string, handle: string) => atom(name, [{ role: "el", handle }]);
  const er = new InquiryEngine(r);
  er.observeNegative("R", el("Invertible", "0"), "zero_no_inv");
  er.observePositive("R", el("AddId", "0"), "zero_add_id");
  er.observePositive("R", el("AddId", "3"), "three_add_id");
  const kept = er.refineBoundary({
    fromBoundary: "R",
    toBoundary: "R_star",
    originalUniversal: forall("x", "R", el("Invertible", "x")),
    targetRelation: "Invertible",
    criterionItem: flip(el("AddId", "x")),
  });
  assert.equal(kept.ok, false);
  if (!kept.ok) {
    assert.equal(kept.violation, "M1-unbound-criterion");
  }
}

function test_m1_indirect_reference_through_registered_links(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Swan", {
    nativeRelations: ["White", "Pale"],
    handles: [
      { id: "swan_402", criterion: "I_Swan", kind: "contingent" },
      { id: "swan_101", criterion: "I_Swan", kind: "contingent" },
    ],
  });
  b.defineBoundary("Swan_Rest", { parents: ["Swan"], handleFilter: (h) => h.id !== "swan_402" });
  const rel = (name: string, handle: string) => atom(name, [{ role: "subject", handle }]);
  const auth = (handle: string) => ({ handle, criterion: "I_Swan" });
  const gen = forall("x", "Swan", rel("White", "x"));
  const base = (): InquiryEngine => {
    const e = new InquiryEngine(b);
    e.observeNegative("Swan", rel("White", "swan_402"), "obs_black", auth("swan_402"));
    e.observePositive("Swan", rel("Pale", "swan_101"), "pale101", auth("swan_101"));
    e.observeNegative("Swan", rel("Pale", "swan_402"), "pale402", auth("swan_402"));
    return e;
  };
  const request = {
    fromBoundary: "Swan",
    toBoundary: "Swan_Rest",
    originalUniversal: gen,
    targetRelation: "White",
    criterionItem: rel("Pale", "x"),
  };

  // Without a registered link the split is admitted.
  assert.equal(base().refineBoundary(request).ok, true);

  // A registered incompatibility ties Pale to White.
  const viaIncompat = base();
  viaIncompat.addIncompatibility("Swan", rel("Pale", "swan_101"), rel("White", "swan_101"));
  const r1 = viaIncompat.refineBoundary(request);
  assert.equal(r1.ok, false);
  if (!r1.ok) {
    assert.equal(r1.violation, "M1-circular");
  }

  // So does a Live conditional between them.
  const viaConditional = base();
  viaConditional.observePositive("Swan", implies(rel("Pale", "swan_101"), rel("White", "swan_101")), "pale_white");
  const r2 = viaConditional.refineBoundary(request);
  assert.equal(r2.ok, false);
  if (!r2.ok) {
    assert.equal(r2.violation, "M1-circular");
  }
}

function test_m1_survivor_exclusion_records_refinement_obligation(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Swan", {
    nativeRelations: ["White", "Lake"],
    handles: [
      { id: "swan_402", criterion: "I_Swan", kind: "contingent" },
      { id: "swan_101", criterion: "I_Swan", kind: "contingent" },
      { id: "swan_777", criterion: "I_Swan", kind: "contingent" },
    ],
  });
  b.defineBoundary("Swan_Rest", { parents: ["Swan"], handleFilter: (h) => h.id !== "swan_402" });
  const rel = (name: string, handle: string) => atom(name, [{ role: "subject", handle }]);
  const auth = (handle: string) => ({ handle, criterion: "I_Swan" });
  const e = new InquiryEngine(b);
  e.observeNegative("Swan", rel("White", "swan_402"), "obs_black", auth("swan_402"));
  e.observePositive("Swan", rel("Lake", "swan_101"), "lake101", auth("swan_101"));
  e.observeNegative("Swan", rel("Lake", "swan_402"), "lake402", auth("swan_402"));
  // swan_777's δ is Open, so it stays in Swan_Rest.
  const res = e.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: "Swan_Rest",
    originalUniversal: forall("x", "Swan", rel("White", "x")),
    targetRelation: "White",
    criterionItem: rel("Lake", "x"),
  });
  assert.equal(res.ok, true);
  assert.deepEqual(e.evaluate().refinementObligations(), []);

  // Later evidence excludes δ(swan_777): the refinement now owes a revision.
  e.observeNegative("Swan", rel("Lake", "swan_777"), "lake777", auth("swan_777"));
  const obligations = e.evaluate().refinementObligations();
  assert.deepEqual(
    obligations.map((o) => [o.fromBoundary, o.toBoundary, o.handle]),
    [["Swan", "Swan_Rest", "swan_777"]],
  );
  // The archived stage before that evidence still owes nothing.
  assert.deepEqual(e.evaluateAtStage(e.stage - 1).refinementObligations(), []);
}

function test_meet_status_is_three_valued(): void {
  const b = new BoundarySystem();
  b.defineBoundary("World");
  b.defineBoundary("Lab", { parents: ["World"] });
  b.defineBoundary("Field", { parents: ["World"] });
  b.defineBoundary("Sea");
  b.defineBoundary("Shore", { parents: ["Sea"] });
  b.defineBoundary("Deep", { parents: ["Sea"] });
  b.defineBoundary("Moon");
  b.defineBoundary("Crater", { parents: ["Moon"] });
  b.declareDisjoint("Sea", "Moon");

  // Overlap: refinement, a registered meet, or a unique maximal common sub-boundary.
  assert.deepEqual(b.meetStatus("Lab", "World"), { kind: "overlap", meet: "Lab" });
  b.defineBoundary("Tidal", { parents: ["Shore", "Deep"] });
  assert.deepEqual(b.meetStatus("Shore", "Deep"), { kind: "overlap", meet: "Tidal" });
  // Disjoint: declared, inherited from declared ancestors, or ⊥_B.
  assert.deepEqual(b.meetStatus("Sea", "Moon"), { kind: "disjoint" });
  assert.deepEqual(b.meetStatus("Shore", "Crater"), { kind: "disjoint" });
  assert.deepEqual(b.meetStatus("Lab", BOT_BOUNDARY), { kind: "disjoint" });
  // Unknown: nothing registered settles it, and it is not read as disjointness.
  assert.deepEqual(b.meetStatus("Lab", "Field"), { kind: "unknown" });
  assert.deepEqual(b.meetStatus("World", "Sea"), { kind: "unknown" });
  // Several maximal common sub-boundaries still require defineMeet.
  b.defineBoundary("Bench", { parents: ["Lab", "Field"] });
  b.defineBoundary("Plot", { parents: ["Lab", "Field"] });
  assert.throws(() => b.meetStatus("Lab", "Field"), /Ambiguous meet/);
}

function test_overlap_unknown_records_obligation_without_collision(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Lab");
  b.defineBoundary("Field");
  const e = new InquiryEngine(b);
  const p = atom("P");
  e.observePositive("Lab", p, "lab");
  e.observeNegative("Field", p, "field");

  // An unknown overlap produces no Collision, but the possible conflict is recorded.
  let snap = e.evaluate();
  assert.equal(snap.isCollisionFree(), true);
  assert.deepEqual(snap.overlapObligations(), [{ left: "Lab", right: "Field", itemKey: "P()" }]);

  // Declared disjointness settles it: no obligation remains.
  const bDisjoint = b.clone();
  bDisjoint.declareDisjoint("Lab", "Field");
  const eDisjoint = new InquiryEngine(bDisjoint);
  eDisjoint.observePositive("Lab", p, "lab");
  eDisjoint.observeNegative("Field", p, "field");
  assert.deepEqual(eDisjoint.evaluate().overlapObligations(), []);
  assert.equal(eDisjoint.evaluate().isCollisionFree(), true);

  // A registered common sub-boundary settles the overlap the other way: the conflict collides there.
  b.defineBoundary("LabField", { parents: ["Lab", "Field"] });
  snap = e.evaluate();
  assert.deepEqual(snap.overlapObligations(), []);
  assert.equal(snap.localStatus("LabField", p), "Collision");
}

function test_cover_revalidation_marks_invalid_and_unverified_covers(): void {
  const P = atom("P");
  const Q = atom("Q");
  const PQ = or(P, Q);
  const build = (order: "cover-first" | "boundary-first") => {
    const b = new BoundarySystem();
    b.defineBoundary("B");
    b.defineBoundary("C1", { parents: ["B"] });
    b.defineBoundary("C2", { parents: ["B"] });
    b.declareDisjoint("C1", "C2");
    const e = new InquiryEngine(b);
    const addB3 = (): void => {
      b.defineBoundary("B3", { parents: ["B"] });
      b.declareDisjoint("B3", "C1");
      b.declareDisjoint("B3", "C2");
    };
    if (order === "boundary-first") {
      addB3();
    }
    const id = e.witnessCover("B", ["C1", "C2"], "cov");
    if (order === "cover-first") {
      addB3();
    }
    e.observePositive("C1", P, "p1");
    e.observePositive("C2", Q, "q2");
    return { b, e, id };
  };

  // Audit reproduction R2: B3 ⊑ B is disjoint from every cell, so the cover is invalid and
  // witnesses nothing; the disjunction it grounded on B and B3 falls back to Open.
  const { b, e, id } = build("cover-first");
  assert.equal(id, "cov");
  assert.deepEqual(b.coverValidity("cov"), { kind: "invalid", witnesses: ["B3"] });
  assert.equal(b.isWitnessedCover("B", ["C1", "C2"]), false);
  let snap = e.evaluate([PQ]);
  assert.deepEqual(snap.coverObligations(), [
    { coverId: "cov", target: "B", cells: ["C1", "C2"], validity: "invalid", witnesses: ["B3"] },
  ]);
  assert.equal(snap.localStatus("B", PQ), "Open");
  assert.equal(snap.localStatus("B3", PQ), "Open");
  // Excluding both disjuncts on B3 now excludes the disjunction there, and nothing collides.
  e.observeNegative("B3", P, "np3");
  e.observeNegative("B3", Q, "nq3");
  snap = e.evaluate([PQ]);
  assert.equal(snap.localStatus("B3", PQ), "Excluded");
  assert.equal(snap.isCollisionFree(), true);

  // Re-validation does not depend on whether the cover or the refuting boundary came first.
  const other = build("boundary-first");
  other.e.observeNegative("B3", P, "np3");
  other.e.observeNegative("B3", Q, "nq3");
  const otherSnap = other.e.evaluate([PQ]);
  for (const bd of ["B", "C1", "C2", "B3"]) {
    for (const it of [P, Q, PQ]) {
      assert.equal(otherSnap.localStatus(bd, it), snap.localStatus(bd, it));
    }
  }
  assert.deepEqual(otherSnap.coverObligations(), snap.coverObligations());

  // Unverified: B4 ⊑ B has an unknown overlap with both cells. The cover still witnesses, owes an
  // obligation, and is left out when only verified covers are asked for.
  const u = new BoundarySystem();
  u.defineBoundary("B");
  u.defineBoundary("C1", { parents: ["B"] });
  u.defineBoundary("C2", { parents: ["B"] });
  u.declareDisjoint("C1", "C2");
  const eu = new InquiryEngine(u);
  eu.witnessCover("B", ["C1", "C2"], "cov");
  u.defineBoundary("B4", { parents: ["B"] });
  assert.deepEqual(u.coverValidity("cov"), { kind: "unverified", witnesses: ["B4"] });
  assert.equal(u.isWitnessedCover("B", ["C1", "C2"]), true);
  assert.equal(u.isWitnessedCover("B", ["C1", "C2"], { verifiedOnly: true }), false);
  eu.observePositive("C1", P, "p1");
  eu.observePositive("C2", Q, "q2");
  snap = eu.evaluate([PQ]);
  assert.equal(snap.localStatus("B", PQ), "Grounded");
  assert.deepEqual(
    snap.coverObligations().map((o) => [o.coverId, o.validity, o.witnesses]),
    [["cov", "unverified", ["B4"]]],
  );
  // A registered common sub-boundary of B4 and C2 settles the overlap, and the cover is valid.
  u.defineBoundary("B4C2", { parents: ["B4", "C2"] });
  assert.deepEqual(u.coverValidity("cov"), { kind: "valid" });
  assert.deepEqual(eu.evaluate([PQ]).coverObligations(), []);

  // A derived cover is judged as a registered one is: {C1, C2} ▷ B is unverified and {D1} ▷ C1 is
  // valid, but X refutes their composite {D1, C2} ▷ B, which is therefore not derived, and no base
  // change to X comes out empty. The unverified source already names X in its obligation.
  const t = new BoundarySystem();
  t.defineBoundary("B");
  t.defineBoundary("C1", { parents: ["B"] });
  t.defineBoundary("C2", { parents: ["B"] });
  t.declareDisjoint("C1", "C2");
  t.defineBoundary("D1", { parents: ["C1"] });
  t.defineBoundary("X", { parents: ["B"] });
  t.declareDisjoint("X", "C2");
  t.declareDisjoint("X", "D1");
  const outer = t.registerCover("B", ["C1", "C2"]);
  const inner = t.registerCover("C1", ["D1"]);
  assert.deepEqual(t.coverValidity(outer), { kind: "unverified", witnesses: ["X"] });
  assert.deepEqual(t.coverValidity(inner), { kind: "valid" });
  assert.equal(t.isWitnessedCover("B", ["C1", "C2"]), true);
  assert.equal(t.isWitnessedCover("C1", ["D1"]), true);
  assert.equal(t.isWitnessedCover("B", ["D1", "C2"]), false);
  assert.deepEqual(t.witnessedCoversOf("X"), [["X"]]);
}

function test_withdraw_cancels_constraints_purely(): void {
  const h = (id: string) => ({ id, criterion: `I(${id})`, kind: "structural" as const });
  const b = new BoundarySystem();
  b.defineBoundary("B");
  b.defineBoundary("C1", { parents: ["B"] });
  b.defineBoundary("C2", { parents: ["B"] });
  b.declareDisjoint("C1", "C2");
  b.defineBoundary("D", { nativeRelations: ["R"], handles: [h("t1")] });
  const A = atom("A");
  const C = atom("C");
  const X = atom("X");
  const P = atom("P");
  const Q = atom("Q");
  const PQ = or(P, Q);
  const r = (x: string) => atom("R", [{ role: "arg", handle: x }]);
  const allR = forall("x", "D", r("x"));

  const e = new InquiryEngine(b);
  e.observePositive("B", A, "wa");
  e.observePositive("C1", P, "p1");
  e.observePositive("C2", Q, "q2");
  e.observePositive("D", r("t1"), "wr");
  const inc = e.addIncompatibility("B", A, C);
  const col = e.addStructuralCollapse("B", X, "collapse_x");
  const cov = e.witnessCover("B", ["C1", "C2"]);
  const clo = e.closeDomain("D");
  assert.equal(col, "collapse_x");
  assert.equal(new Set([inc, col, cov, clo]).size, 4);
  assert.deepEqual(
    [inc, col, cov, clo].map((id) => e.constraintKind(id)),
    ["incompatibility", "collapse", "cover", "closure"],
  );
  const before = e.stage;
  let snap = e.evaluate([PQ, allR]);
  assert.equal(snap.localStatus("B", C), "Excluded");
  assert.equal(snap.localStatus("B", X), "Excluded");
  assert.equal(snap.localStatus("B", PQ), "Grounded");
  assert.equal(snap.localStatus("D", allR), "Grounded");

  // Each Withdraw removes its constraint from C_B and adds nothing: what it supported is Open.
  for (const id of [inc, col, cov, clo]) {
    assert.equal(e.withdraw(id), true);
    assert.equal(e.transitionLog.at(-1), `Σ${e.stage}:Withdraw(${id})`);
    assert.equal(e.constraintKind(id), undefined);
  }
  assert.equal(e.stage, before + 4);
  snap = e.evaluate([PQ, allR]);
  for (const [bd, it] of [["B", C], ["B", X], ["B", PQ], ["D", allR]] as const) {
    assert.equal(snap.localStatus(bd, it), "Open");
  }
  assert.equal(snap.localStatus("B", A), "Grounded");
  assert.equal(b.isWitnessedCover("B", ["C1", "C2"]), false);
  assert.equal(e.isDomainClosed("D"), false);
  // The items the withdrawn constraints named stay tracked.
  const tracked = new Set(e.evaluate().universe().map(itemKey));
  for (const it of [C, X, implies(X, bottom())]) {
    assert.ok(tracked.has(itemKey(it)), `${itemKey(it)} stays tracked`);
  }
  // The archived stage before the withdrawals keeps every constraint in force.
  const archived = e.evaluateAtStage(before, [PQ, allR]);
  assert.equal(archived.localStatus("B", C), "Excluded");
  assert.equal(archived.localStatus("B", X), "Excluded");
  assert.equal(archived.localStatus("B", PQ), "Grounded");
  assert.equal(archived.localStatus("D", allR), "Grounded");

  // An unknown or already withdrawn identifier changes nothing, and identifiers are not reused.
  assert.equal(e.withdraw(inc), false);
  assert.equal(e.withdraw("nope"), false);
  assert.equal(e.stage, before + 4);
  assert.throws(() => e.addIncompatibility("B", A, C, inc), /already used/);
  // Under monotone growth (item 13), Withdraw is forbidden as Retract is.
  const mono = new InquiryEngine(b.clone(), { monotoneOnly: true });
  const monoId = mono.addIncompatibility("B", A, C);
  assert.throws(() => mono.withdraw(monoId), /Withdraw is forbidden/);
}

test("boundary meet-semilattice and non-witnessing bottom", test_boundary_meet_semilattice_and_non_witnessing_bottom);
test("finitary Grothendieck covers meet-stability and non-vacuity", test_finitary_grothendieck_covers_meet_stability_and_non_vacuity);
test("co-reference multi-granularity isolation and anti-equivocation", test_coreference_multi_granularity_and_anti_equivocation);
test("inquiry updates retract non-commutativity and M1/M2", test_inquiry_updates_retract_non_commutativity_and_m1_m2);
test("M1(iii) excess content blocks disguised proxies and preserves structural singularities", test_m1_iii_excess_content_blocks_disguised_proxies_and_preserves_structural_singularities);
test(
  "core engine congruence forall-elim domainConstraint and semilattice consistency",
  test_core_engine_congruence_forall_elim_domain_constraint_and_semilattice_consistency,
);
test("domain monotonicity rejects sub-boundary handles", test_domain_monotonicity_rejects_sub_boundary_handles);
test("CloseDomain gates enumerative quantifiers", test_close_domain_gates_enumerative_quantifiers);
test("M1 binding rejects criteria not shown to exclude excised handles", test_m1_binding_rejects_criteria_not_shown_to_exclude_excised_handles);
test("M1 indirect reference through registered links", test_m1_indirect_reference_through_registered_links);
test("M1 survivor exclusion records a refinement obligation", test_m1_survivor_exclusion_records_refinement_obligation);
test("meet status is three-valued", test_meet_status_is_three_valued);
test("overlap unknown records an obligation without collision", test_overlap_unknown_records_obligation_without_collision);
test("cover revalidation marks invalid and unverified covers", test_cover_revalidation_marks_invalid_and_unverified_covers);
test("withdraw cancels constraints purely", test_withdraw_cancels_constraints_purely);
test("registered meet is the greatest lower bound", test_registered_meet_is_the_greatest_lower_bound);
