import assert from "node:assert/strict";
import { test } from "node:test";
import { BoundarySystem } from "../src/boundary.ts";
import { InquiryEngine, isWellFoundedGraph } from "../src/engine.ts";
import {
  and,
  atom,
  bottom,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  structImposs,
} from "../src/syntax.ts";

function test_dual_polarity_statuses_and_well_founded_dag_rejects_cycles(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  const engine = new InquiryEngine(b);

  const pOpen = atom("OpenClaim");
  const pGrounded = atom("GroundedClaim");
  const pExcluded = atom("ExcludedClaim");
  const pCollided = atom("CollidedClaim");

  engine.observePositive("B", pGrounded, "w_g");
  engine.observeNegative("B", pExcluded, "w_e");
  engine.observePositive("B", pCollided, "w_c1");
  engine.observeNegative("B", pCollided, "w_c2");

  const snap = engine.evaluate([pOpen]);
  assert.equal(snap.statusOf("B", pOpen), "Open");
  assert.equal(snap.statusOf("B", pGrounded), "Grounded");
  assert.equal(snap.statusOf("B", pExcluded), "Excluded");
  assert.equal(snap.statusOf("B", pCollided), "Collision");

  // Well-Foundedness Law: mutual-support cycles (A -> B, B -> A) confer zero grounding
  const cyclicGraph = new Map<string, readonly string[]>([
    ["A", ["B"]],
    ["B", ["A"]],
  ]);
  const emptyLeaves = new Set<string>();
  assert.equal(isWellFoundedGraph(cyclicGraph, emptyLeaves, "A"), false);
  assert.equal(isWellFoundedGraph(cyclicGraph, emptyLeaves, "B"), false);

  // Acyclic DAG anchored in active base leaf E is well-founded
  const acyclicGraph = new Map<string, readonly string[]>([
    ["C", ["A", "B"]],
    ["A", ["E"]],
    ["B", ["E"]],
  ]);
  assert.equal(isWellFoundedGraph(acyclicGraph, new Set(["E"]), "C"), true);
}

function test_symmetric_downward_heredity_and_disjoint_zero_leakage(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B_all");
  b.defineBoundary("B_1atm", { parents: ["B_all"] });
  b.defineBoundary("B_2atm", { parents: ["B_all"] });
  b.declareDisjoint("B_1atm", "B_2atm");

  const engine = new InquiryEngine(b);
  const heat100 = atom("Heat100");
  const boils = atom("Boils");
  const ruleBroad = implies(heat100, boils);

  engine.observePositive("B_all", ruleBroad, "w1");
  engine.observePositive("B_2atm", heat100, "w5");
  engine.observeNegative("B_2atm", boils, "w6");

  const snap = engine.evaluate();
  // Positive ruleBroad inherits downward to both B_1atm and B_2atm
  assert.equal(snap.allGrounds("B_1atm", "+", ruleBroad).length, 1);
  // Counterexample on B_2atm triggers local -(Heat100 -> Boils) on B_2atm ONLY (zero leakage to B_1atm!)
  assert.equal(snap.statusOf("B_2atm", ruleBroad), "Collision");
  assert.equal(snap.allGrounds("B_1atm", "-", ruleBroad).length, 0);
  assert.equal(snap.statusOf("B_1atm", ruleBroad), "Grounded");
}

function test_quarantine_upstream_obstruction_and_selective_survival(): void {
  // Full worked-examples §1 boiling-point scenario: Σ0 -> Σ1 -> Σ2
  const b = new BoundarySystem();
  b.defineBoundary("B_all", {
    nativeRelations: ["Pressure", "Heat100", "Boils", "Cook"],
    handles: [
      { id: "1atm", criterion: "I_P(1atm)", kind: "structural" },
      { id: "2atm", criterion: "I_P(2atm)", kind: "structural" },
    ],
  });
  b.defineBoundary("B_1atm", {
    parents: ["B_all"],
    handles: [{ id: "1atm", criterion: "I_P(1atm)", kind: "structural" }],
  });
  b.defineBoundary("B_2atm", {
    parents: ["B_all"],
    handles: [{ id: "2atm", criterion: "I_P(2atm)", kind: "structural" }],
  });
  b.declareDisjoint("B_1atm", "B_2atm");

  const engine = new InquiryEngine(b);
  const heatAt = (p: string) => atom("Heat100", [{ role: "pressure", handle: p }]);
  const boilsAt = (p: string) => atom("Boils", [{ role: "pressure", handle: p }]);
  const heat100 = heatAt("1atm");
  const boils = boilsAt("1atm");
  const cook = atom("Cook", [{ role: "item", handle: "pasta" }]);
  const ruleBroad = implies(heat100, boils);
  const ruleCook = implies(boils, cook);
  const genAll = forall("p", "B_all", implies(heatAt("p"), boilsAt("p")));
  const gen1Atm = forall("p", "B_1atm", implies(heatAt("p"), boilsAt("p")));

  // Stage Σ0: Initial Grounding
  engine.observePositive("B_all", ruleBroad, "w1");
  engine.observePositive("B_all", ruleCook, "w2");
  engine.observePositive("B_1atm", heat100, "w3");
  engine.observePositive("B_1atm", boils, "w_emp");
  engine.observePositive("B_all", genAll, "w4");

  const snap0 = engine.evaluate([cook, genAll]);
  assert.equal(snap0.isCollisionFree(), true);
  assert.equal(snap0.liveGrounds("B_1atm", "+", boils).length, 2); // π1 and π2
  assert.equal(snap0.liveGrounds("B_1atm", "+", cook).length, 2);

  // Stage Σ1: Counterexample at 2 atm
  engine.observePositive("B_2atm", heat100, "w5");
  engine.observeNegative("B_2atm", boils, "w6");
  engine.observePositive("B_all", heatAt("2atm"), "w5_all");
  engine.observeNegative("B_all", boilsAt("2atm"), "w6_all");

  const snap1 = engine.evaluate([cook, genAll]);
  assert.equal(snap1.statusOf("B_2atm", ruleBroad), "Collision");
  assert.equal(snap1.isObstructed("B_all", ruleBroad), true);
  assert.equal(snap1.isLive("B_all", "+", ruleBroad), false);
  assert.equal(snap1.statusOf("B_all", genAll), "Collision");
  assert.ok(snap1.revisionObligations().length >= 2);

  // Selective Quarantine: π1 loses Live authority, while π2 (w_emp) and Cook via π2 remain Live!
  const boilsLive1 = snap1.liveGrounds("B_1atm", "+", boils);
  assert.equal(boilsLive1.length, 1);
  assert.deepEqual(
    boilsLive1[0]?.provenance.kind === "base" ? boilsLive1[0].provenance.baseId : "",
    "w_emp",
  );
  assert.equal(snap1.liveGrounds("B_1atm", "+", cook).length, 1);
  assert.equal(snap1.isLive("B_1atm", "+", cook), true);

  // Stage Σ2: Retract overbroad rules + RefineBoundary obeying M1 & M2
  engine.retract("w1");
  engine.retract("w4");
  const refine = engine.refineBoundary({
    fromBoundary: "B_all",
    toBoundary: "B_1atm",
    originalUniversal: genAll,
    targetRelation: "Boils",
    criterionItem: atom("Pressure", [
      { role: "target", handle: "p" },
      { role: "value", handle: "1atm" },
    ]),
  });
  assert.equal(refine.ok, true);

  engine.observePositive("B_1atm", ruleBroad, "w1_prime");
  engine.observePositive("B_1atm", gen1Atm, "w4_prime");

  const snap2 = engine.evaluate([cook, genAll, gen1Atm]);
  // M2 check: (B_all, Gen_all) remains Excluded (-); narrowed Gen_1atm is Grounded (+)
  assert.equal(snap2.statusOf("B_all", genAll), "Excluded");
  assert.equal(snap2.statusOf("B_1atm", gen1Atm), "Grounded");
  assert.equal(snap2.isLive("B_1atm", "+", cook), true);
  assert.equal(snap2.isCollisionFree(), true);
}

function test_structural_rules_scoped_cut_and_horizontal_contraction(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  b.defineBoundary("B1", { parents: ["B"] });
  b.defineBoundary("B2", { parents: ["B"] });
  b.defineBoundary("B12", { parents: ["B1", "B2"] });

  const engine = new InquiryEngine(b);
  const x = atom("X");
  const a = atom("A");
  const c = atom("C");
  const e = atom("E");
  const arbitraryNoise = atom("MoonIsCheese");

  // Horizontal Contraction: one witness w_x used twice across two conditionals
  engine.observePositive("B1", x, "w_x");
  engine.observePositive("B2", implies(x, a), "w_xa");
  engine.observePositive("B2", implies(x, c), "w_xc");
  engine.observePositive("B", implies(and(a, c), e), "w_ace");

  const snapOk = engine.evaluate([e, arbitraryNoise]);
  assert.equal(snapOk.isLive("B12", "+", a), true);
  assert.equal(snapOk.isLive("B12", "+", c), true);
  assert.equal(snapOk.isLive("B12", "+", e), true);
  assert.equal(snapOk.statusOf("B12", arbitraryNoise), "Open");

  // Counterexample -A on B12 refutes (X → A), obstructing B2 and preventing ghost +A on B12;
  // Scoped Cut still blocks E and No Explosion holds (arbitraryNoise stays Open).
  engine.observeNegative("B12", a, "refute_a");
  const snapBlocked = engine.evaluate([e, arbitraryNoise]);
  assert.equal(snapBlocked.statusOf("B12", implies(x, a)), "Collision");
  assert.equal(snapBlocked.isObstructed("B2", implies(x, a)), true);
  assert.equal(snapBlocked.statusOf("B12", a), "Excluded");
  assert.equal(snapBlocked.isLive("B12", "+", e), false);
  assert.equal(snapBlocked.statusOf("B12", arbitraryNoise), "Open");

  // Direct base +A on B12 collides node A itself while still blocking E via Scoped Cut
  engine.observePositive("B12", a, "w_a_direct");
  const snapDirect = engine.evaluate([e, arbitraryNoise]);
  assert.equal(snapDirect.statusOf("B12", a), "Collision");
  assert.equal(snapDirect.isLive("B12", "+", e), false);
  assert.equal(snapDirect.statusOf("B12", arbitraryNoise), "Open");
}

function test_connective_and_quantifier_polarity_rules_with_cover_gluing(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Z", {
    nativeRelations: ["IsEven", "IsOdd", "IsInt", "Red", "Green", "OpenItem"],
    handles: [
      { id: "n1", criterion: "I_Z(1)", kind: "structural" },
      { id: "n2", criterion: "I_Z(2)", kind: "structural" },
    ],
  });
  b.defineBoundary("Even", {
    parents: ["Z"],
    handles: [{ id: "n2", criterion: "I_Z(2)", kind: "structural" }],
  });
  b.defineBoundary("Odd", {
    parents: ["Z"],
    handles: [{ id: "n1", criterion: "I_Z(1)", kind: "structural" }],
  });
  b.declareDisjoint("Even", "Odd");
  b.registerCover("Z", ["Even", "Odd"]);

  const engine = new InquiryEngine(b);
  const isEven = atom("IsEven");
  const isOdd = atom("IsOdd");
  const isInt = atom("IsInt");
  const openItem = atom("OpenItem");
  const red = atom("Red");
  const green = atom("Green");
  const sqCircle = atom("SquareCircle");

  // Bottom ⊥ is never witnessed and always structurally excluded
  const bot = bottom();

  // Material incompatibility Red ⊥_Z Green
  engine.addIncompatibility("Z", red, green);
  engine.observePositive("Z", red, "w_red");

  // Structural impossibility B ⊓ [SquareCircle] = ⊥_B (no DNE!)
  engine.addStructuralCollapse("Z", sqCircle);

  // D2 Cover-Witnessed Disjunction + ∨E Cover Gluing on Z = Even ⊔ Odd
  engine.observePositive("Even", isEven, "w_even");
  engine.observePositive("Odd", isOdd, "w_odd");
  engine.observePositive("Z", implies(isEven, isInt), "w_e_int");
  engine.observePositive("Z", implies(isOdd, isInt), "w_o_int");

  // Scoped Conditional: -OpenItem alone must NOT fabricate +(OpenItem -> IsInt)
  const negAOnly = atom("RefutedOnly");
  engine.observeNegative("Z", negAOnly, "w_neg_only");

  // Quantifiers: ∀ and ∃
  const pX = (h: string) => atom("Prop", [{ role: "arg", handle: h }]);
  engine.observePositive("Z", pX("n2"), "w_pn2");
  engine.observeNegative("Z", pX("n1"), "w_not_pn1");

  const disj = or(isEven, isOdd);
  const lemOpen = or(openItem, flip(openItem));
  const conjEvenInt = and(isEven, isInt);
  const univP = forall("x", "Z", pX("x"));
  const existP = exists("x", "Z", pX("x"));
  const dneTarget = structImposs(structImposs(sqCircle));

  const snap = engine.evaluate([
    bot,
    flip(red),
    dneTarget,
    disj,
    lemOpen,
    conjEvenInt,
    implies(negAOnly, isInt),
    univP,
    existP,
  ]);

  assert.equal(snap.statusOf("Z", bot), "Excluded");
  assert.equal(snap.allGrounds("Z", "+", bot).length, 0);
  assert.equal(snap.statusOf("Z", green), "Excluded");
  assert.equal(snap.statusOf("Z", flip(red)), "Excluded");
  assert.equal(snap.statusOf("Z", structImposs(sqCircle)), "Grounded");
  assert.equal(snap.statusOf("Z", sqCircle), "Excluded");
  assert.equal(snap.allGrounds("Z", "+", sqCircle).length, 0);

  // D2 disjunction and ∨E gluing succeed; LEM on Open item is refused
  assert.equal(snap.statusOf("Z", disj), "Grounded");
  assert.equal(snap.isLive("Z", "+", disj), true);
  assert.equal(snap.statusOf("Z", isInt), "Grounded");
  assert.equal(snap.isLive("Z", "+", isInt), true);
  assert.equal(snap.statusOf("Z", lemOpen), "Open");

  // Conjunction on Even holds (+IsEven and inherited +IsInt); on Odd IsEven is Open so conjunction is Open
  assert.equal(snap.statusOf("Even", conjEvenInt), "Grounded");
  assert.equal(snap.statusOf("Odd", conjEvenInt), "Open");

  // Non-vacuous conditional: -A alone does not witness +(A → C)
  assert.equal(snap.statusOf("Z", implies(negAOnly, isInt)), "Open");

  // Quantifiers: concrete witness n2 -> +∃; concrete counterexample n1 -> -∀
  assert.equal(snap.statusOf("Z", existP), "Grounded");
  assert.equal(snap.statusOf("Z", univP), "Excluded");
}

function test_stratified_quarantine_eliminates_ghost_collisions_and_preserves_symmetric_conflict(): void {
  const a = atom("A");
  const c = atom("C");

  // Part A1: Single-boundary flip-elim collision (+A, +~A, +(A → C), -C) blocks ghost +C
  const bFlip = new BoundarySystem();
  bFlip.defineBoundary("B");
  const eFlip = new InquiryEngine(bFlip);
  eFlip.observePositive("B", a, "w_a");
  eFlip.observePositive("B", flip(a), "w_flip_a");
  eFlip.observePositive("B", implies(a, c), "w_ac");
  eFlip.observeNegative("B", c, "w_nc");

  const snapFlip = eFlip.evaluate([a, c]);
  assert.equal(snapFlip.statusOf("B", a), "Collision");
  assert.equal(snapFlip.isLive("B", "+", a), false);
  assert.equal(snapFlip.statusOf("B", c), "Excluded");
  assert.equal(snapFlip.isLive("B", "-", c), true);
  assert.equal(snapFlip.allGrounds("B", "+", c).length, 0);

  // Part A2: Super-boundary obstruction delay (B_sub ⊑ B_all) blocks ghost +C on B_all
  const bSup = new BoundarySystem();
  bSup.defineBoundary("B_all");
  bSup.defineBoundary("B_sub", { parents: ["B_all"] });
  const eSup = new InquiryEngine(bSup);
  eSup.observePositive("B_all", a, "w_a");
  eSup.observePositive("B_all", implies(a, c), "w_ac");
  eSup.observeNegative("B_sub", a, "w_na");
  eSup.observeNegative("B_all", c, "w_nc");

  const snapSup = eSup.evaluate([a, c]);
  assert.equal(snapSup.statusOf("B_sub", a), "Collision");
  assert.equal(snapSup.isObstructed("B_all", a), true);
  assert.equal(snapSup.statusOf("B_all", c), "Excluded");
  assert.equal(snapSup.isLive("B_all", "-", c), true);
  assert.equal(snapSup.allGrounds("B_all", "+", c).length, 0);
  assert.equal(
    snapSup.revisionObligations().some((r) => r.boundary === "B_sub" && r.itemKey === itemKey(a)),
    true,
  );
  assert.equal(
    snapSup.revisionObligations().every((r) => r.itemKey !== itemKey(c)),
    true,
  );

  // Part B: Sub-boundary ghost collision (B_all +(Heat -> Boils), B_2atm refutes it, B_1atm has +Heat and -Boils)
  const bSub = new BoundarySystem();
  bSub.defineBoundary("B_all");
  bSub.defineBoundary("B_1atm", { parents: ["B_all"] });
  bSub.defineBoundary("B_2atm", { parents: ["B_all"] });
  bSub.declareDisjoint("B_1atm", "B_2atm");

  const eSub = new InquiryEngine(bSub);
  const heat = atom("Heat");
  const boils = atom("Boils");
  const rule = implies(heat, boils);
  eSub.observePositive("B_all", rule, "w_rule");
  eSub.observePositive("B_2atm", heat, "w_h2");
  eSub.observeNegative("B_2atm", boils, "w_nb2");
  eSub.observePositive("B_1atm", heat, "w_h1");
  eSub.observeNegative("B_1atm", boils, "w_nb1");

  const snapSub = eSub.evaluate([rule, boils]);
  assert.equal(snapSub.statusOf("B_2atm", rule), "Collision");
  assert.equal(snapSub.isObstructed("B_all", rule), true);
  assert.equal(snapSub.statusOf("B_1atm", boils), "Excluded");
  assert.equal(snapSub.isLive("B_1atm", "-", boils), true);
  assert.equal(snapSub.allGrounds("B_1atm", "+", boils).length, 0);

  // Part C: Multi-step reinstatement via directional rule defeat
  const bRein = new BoundarySystem();
  bRein.defineBoundary("B_all");
  bRein.defineBoundary("B_1", { parents: ["B_all"] });
  bRein.defineBoundary("B_2", { parents: ["B_all"] });
  bRein.declareDisjoint("B_1", "B_2");

  const eRein = new InquiryEngine(bRein);
  const ice = atom("Ice");
  const cold = atom("Cold");
  const heatToBoils = implies(heat, boils);
  eRein.observePositive("B_all", heatToBoils, "w_rule1");
  eRein.observePositive("B_2", heat, "w_h2");
  eRein.observeNegative("B_2", boils, "w_nb2");
  eRein.observePositive("B_1", heat, "w_h1");
  eRein.observePositive("B_1", ice, "w_ice");
  eRein.addIncompatibility("B_1", boils, ice);
  eRein.observePositive("B_1", implies(ice, cold), "w_rule2");

  const snapRein = eRein.evaluate([heatToBoils, boils, ice, cold]);
  assert.equal(snapRein.statusOf("B_2", heatToBoils), "Collision");
  assert.equal(snapRein.isObstructed("B_all", heatToBoils), true);
  assert.equal(snapRein.statusOf("B_1", ice), "Grounded");
  assert.equal(snapRein.isLive("B_1", "+", ice), true);
  assert.equal(snapRein.statusOf("B_1", boils), "Excluded");
  assert.equal(snapRein.isLive("B_1", "-", boils), true);
  assert.equal(snapRein.allGrounds("B_1", "+", boils).length, 0);
  assert.equal(snapRein.statusOf("B_1", cold), "Grounded");
  assert.equal(snapRein.isLive("B_1", "+", cold), true);

  // Part D: Symmetric mutual conflict (+A, +C, A ⊥ C) preserves Collision on both
  const bSym = new BoundarySystem();
  bSym.defineBoundary("B");
  const eSym = new InquiryEngine(bSym);
  eSym.addIncompatibility("B", a, c);
  eSym.observePositive("B", a, "wa");
  eSym.observePositive("B", c, "wc");

  const snapSym = eSym.evaluate([a, c]);
  assert.equal(snapSym.statusOf("B", a), "Collision");
  assert.equal(snapSym.statusOf("B", c), "Collision");
  assert.equal(snapSym.isLive("B", "+", a), false);
  assert.equal(snapSym.isLive("B", "+", c), false);
}

function test_bottom_non_witnessing_guard_and_imposs_contraposition(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  const engine = new InquiryEngine(b);

  // Guard: direct positive witness of bottom on non-empty boundary is rejected
  assert.throws(
    () => engine.observePositive("B", bottom(), "bad_bot"),
    /admits no positive witness/,
  );

  // Uncontested +(A → ⊥) derives -A without enabling DNE from ((A2 → ⊥) → ⊥)
  const a1 = atom("UncontestedImposs");
  const a2 = atom("DoubleImposs");
  engine.observePositive("B", structImposs(a1), "w_imp1");
  engine.observePositive("B", structImposs(structImposs(a2)), "w_imp2");

  const snap1 = engine.evaluate([a1, a2, structImposs(a2)]);
  assert.equal(snap1.statusOf("B", a1), "Excluded");
  assert.equal(snap1.isLive("B", "-", a1), true);
  assert.equal(snap1.statusOf("B", structImposs(a2)), "Excluded");
  assert.equal(snap1.statusOf("B", a2), "Open");
  assert.equal(snap1.allGrounds("B", "+", a2).length, 0);

  // Conflicting +(A3 → ⊥) and +A3 puts (B, A3 → ⊥) into Collision and emits zero +⊥ entries
  const bConf = new BoundarySystem();
  bConf.defineBoundary("B");
  const eConf = new InquiryEngine(bConf);
  const a3 = atom("ConflictingItem");
  eConf.observePositive("B", structImposs(a3), "w_imp3");
  eConf.observePositive("B", a3, "w_a3");

  const snapConf = eConf.evaluate([a3, structImposs(a3), bottom()]);
  assert.equal(snapConf.statusOf("B", structImposs(a3)), "Collision");
  assert.equal(snapConf.allGrounds("B", "+", bottom()).length, 0);
  assert.equal(snapConf.statusOf("B", bottom()), "Excluded");
}

test("dual-polarity statuses and well-founded DAG rejects cycles", test_dual_polarity_statuses_and_well_founded_dag_rejects_cycles);
test("symmetric downward heredity and disjoint zero leakage", test_symmetric_downward_heredity_and_disjoint_zero_leakage);
test("quarantine upstream obstruction and selective survival", test_quarantine_upstream_obstruction_and_selective_survival);
test("structural rules Scoped Cut and horizontal Contraction", test_structural_rules_scoped_cut_and_horizontal_contraction);
test("connective and quantifier polarity rules with cover gluing", test_connective_and_quantifier_polarity_rules_with_cover_gluing);
test(
  "stratified quarantine eliminates ghost collisions and preserves symmetric conflict",
  test_stratified_quarantine_eliminates_ghost_collisions_and_preserves_symmetric_conflict,
);
test(
  "bottom non-witnessing guard and structural impossibility contraposition",
  test_bottom_non_witnessing_guard_and_imposs_contraposition,
);
