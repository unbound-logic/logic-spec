import assert from "node:assert/strict";
import { test } from "node:test";
import { BoundarySystem } from "../src/boundary.ts";
import { InquiryEngine } from "../src/engine.ts";
import {
  evaluateClassicalSpecialization,
  verifyIntuitionisticSpecialization,
  verifyMinimalSpecialization,
} from "../src/specializations.ts";
import { and, atom, bottom, equiv, exists, flip, forall, implies, itemKey, or } from "../src/syntax.ts";

function test_four_tier_deductive_spectrum_and_classical_recovery(): void {
  // Tier 2 & 3: UL-Minimal & UL-Intuitionistic (monotoneOnly + No-Gluts)
  const bMin = new BoundarySystem();
  bMin.defineBoundary("B");
  const eMin = new InquiryEngine(bMin, { monotoneOnly: true });
  const aClaim = atom("A");
  eMin.observePositive("B", aClaim, "w_a");

  assert.throws(() => eMin.retract("w_a"), /Retract is forbidden/);
  const minRes = verifyMinimalSpecialization(eMin, [aClaim]);
  assert.equal(minRes.ok, true);
  const intRes = verifyIntuitionisticSpecialization(eMin, [aClaim]);
  assert.equal(intRes.ok, true);
  if (intRes.ok) {
    assert.equal(intRes.exFalsoBottomVerified, true);
  }

  // Tier 4: UL-Classical — worked-examples §4 (Derivations 4A, 4B, 4C)
  // 4A: Non-atomic boundary B with witnessed atomic cover {B*_1, B*_2} ▷ B
  const bCov = new BoundarySystem();
  bCov.defineBoundary("B");
  bCov.defineBoundary("B1_star", { parents: ["B"] });
  bCov.defineBoundary("B2_star", { parents: ["B"] });
  bCov.declareDisjoint("B1_star", "B2_star");
  bCov.registerCover("B", ["B1_star", "B2_star"]);

  const eCov = new InquiryEngine(bCov, { monotoneOnly: true });
  eCov.observePositive("B1_star", aClaim, "w_b1_a");
  eCov.observeNegative("B2_star", aClaim, "w_b2_na");

  const lemItem = or(aClaim, flip(aClaim));
  // Direct UL-Core D2 cover disjunction already witnesses +(A ∨ ~A) on B!
  assert.equal(eCov.evaluate([lemItem]).statusOf("B", lemItem), "Grounded");

  const clCov = evaluateClassicalSpecialization(eCov, "B", [aClaim], [lemItem]);
  assert.equal(clCov.ok, true);
  if (clCov.ok) {
    assert.equal(clCov.results.get(itemKey(lemItem))?.polarity, "+");
    assert.equal(clCov.results.get(itemKey(lemItem))?.bivalent, true);
    assert.equal(clCov.results.get(itemKey(lemItem))?.negCollapseEquivalent, true);
    assert.equal(clCov.vacuousExplosionHolds, true);
  }

  // 4B & 4C on atomic closed boundary B*
  const bAtomic = new BoundarySystem();
  bAtomic.defineBoundary("B_star");
  const eAtomic = new InquiryEngine(bAtomic, { monotoneOnly: true });
  const cClaim = atom("C");
  const pClaim = atom("P");
  const qClaim = atom("Q");

  // 4B: -A and -C -> Open in UL-Core, closed to +(A -> C) in UL-Classical with MP never firing
  eAtomic.observeNegative("B_star", aClaim, "w_neg_a");
  eAtomic.observeNegative("B_star", cClaim, "w_neg_c");

  // 4C: +(P -> Q) and +(~Q) -> Modus Tollens gives +(~P) under UL-Classical
  const pImpliesQ = implies(pClaim, qClaim);
  eAtomic.observePositive("B_star", pImpliesQ, "w_pq");
  eAtomic.observePositive("B_star", flip(qClaim), "w_nq");
  // Fix No-Gaps on P by observing -P (verify Modus Tollens consistency: +P would violate No-Gluts!)
  eAtomic.observeNegative("B_star", pClaim, "w_np");

  const aImpliesC = implies(aClaim, cClaim);
  // In UL-Core, -A ∧ -C leaves (A → C) Open and does not fire MP to produce +C
  const coreSnap = eAtomic.evaluate([aImpliesC, flip(pClaim)]);
  assert.equal(coreSnap.statusOf("B_star", aImpliesC), "Open");
  assert.equal(coreSnap.isLive("B_star", "+", cClaim), false);

  const clAtomic = evaluateClassicalSpecialization(
    eAtomic,
    "B_star",
    [aClaim, cClaim, pClaim, qClaim],
    [aImpliesC, flip(pClaim), pImpliesQ],
  );
  assert.equal(clAtomic.ok, true);
  if (clAtomic.ok) {
    assert.equal(clAtomic.results.get(itemKey(aImpliesC))?.polarity, "+");
    assert.equal(clAtomic.results.get(itemKey(flip(pClaim)))?.polarity, "+");
    assert.equal(clAtomic.results.get(itemKey(flip(pClaim)))?.negCollapseEquivalent, true);
  }

  // Verify Modus Tollens impossibility: if +P had been asserted instead of -P, No-Gluts catches the collision
  const eConflict = new InquiryEngine(bAtomic, { monotoneOnly: true });
  eConflict.observePositive("B_star", pImpliesQ, "w_pq");
  eConflict.observePositive("B_star", flip(qClaim), "w_nq");
  eConflict.observePositive("B_star", pClaim, "w_p");
  const clConflict = evaluateClassicalSpecialization(
    eConflict,
    "B_star",
    [pClaim, qClaim],
    [flip(pClaim)],
  );
  assert.equal(clConflict.ok, false);
}

function test_classical_atomic_cover_2k_boolean_algebra_reporting(): void {
  const bCov = new BoundarySystem();
  bCov.defineBoundary("B");
  bCov.defineBoundary("B1_star", { parents: ["B"] });
  bCov.defineBoundary("B2_star", { parents: ["B"] });
  bCov.declareDisjoint("B1_star", "B2_star");
  bCov.registerCover("B", ["B1_star", "B2_star"]);

  const engine = new InquiryEngine(bCov, { monotoneOnly: true });
  const aClaim = atom("A");
  engine.observePositive("B1_star", aClaim, "w_b1_a");
  engine.observeNegative("B2_star", aClaim, "w_b2_na");

  const lemItem = or(aClaim, flip(aClaim));
  const contraItem = and(aClaim, flip(aClaim));
  const res = evaluateClassicalSpecialization(
    engine,
    "B",
    [aClaim],
    [aClaim, lemItem, contraItem],
  );
  assert.equal(res.ok, true);
  if (res.ok) {
    const aVal = res.results.get(itemKey(aClaim));
    assert.equal(aVal?.polarity, "split");
    assert.equal(aVal?.cellPolarities.get("B1_star"), "+");
    assert.equal(aVal?.cellPolarities.get("B2_star"), "-");
    assert.equal(aVal?.bivalent, true);
    assert.equal(aVal?.negCollapseEquivalent, true);

    const lemVal = res.results.get(itemKey(lemItem));
    assert.equal(lemVal?.polarity, "+");
    assert.equal(lemVal?.cellPolarities.get("B1_star"), "+");
    assert.equal(lemVal?.cellPolarities.get("B2_star"), "+");

    const contraVal = res.results.get(itemKey(contraItem));
    assert.equal(contraVal?.polarity, "-");
    assert.equal(contraVal?.cellPolarities.get("B1_star"), "-");
    assert.equal(contraVal?.cellPolarities.get("B2_star"), "-");
  }
}

function test_classical_specialization_guards_compound_exclusions_nogaps_and_frozen(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B_star", {
    nativeRelations: ["P", "D_pred"],
    handles: [
      { id: "a", criterion: "I(a)", kind: "structural" },
      { id: "b", criterion: "I(b)", kind: "structural" },
    ],
  });

  const aClaim = atom("A");
  const cClaim = atom("C");

  // 1. Reject non-monotone engine (UL-Classical requires frozen/monotone Σ)
  const eNonMon = new InquiryEngine(b, { monotoneOnly: false });
  eNonMon.observeNegative("B_star", aClaim, "w_na");
  eNonMon.observeNegative("B_star", cClaim, "w_nc");
  const resNonMon = evaluateClassicalSpecialization(
    eNonMon,
    "B_star",
    [aClaim, cClaim],
    [implies(aClaim, cClaim)],
  );
  assert.equal(resNonMon.ok, false);

  // 2. Reject existing Live compound exclusion conflicting with classical truth table (-(A → C) alongside -A, -C)
  const eCompExcl = new InquiryEngine(b, { monotoneOnly: true });
  eCompExcl.observeNegative("B_star", aClaim, "w_na");
  eCompExcl.observeNegative("B_star", cClaim, "w_nc");
  eCompExcl.observeNegative("B_star", implies(aClaim, cClaim), "w_neg_imp");
  const resCompExcl = evaluateClassicalSpecialization(
    eCompExcl,
    "B_star",
    [aClaim, cClaim],
    [implies(aClaim, cClaim)],
  );
  assert.equal(resCompExcl.ok, false);

  // 3. Reject queryItems mentioning an Open atom or Open equiv omitted from `atoms`
  const eGaps = new InquiryEngine(b, { monotoneOnly: true });
  eGaps.observeNegative("B_star", aClaim, "w_na");
  const resOpenAtom = evaluateClassicalSpecialization(
    eGaps,
    "B_star",
    [aClaim],
    [implies(aClaim, atom("UncheckedOpen"))],
  );
  assert.equal(resOpenAtom.ok, false);

  const resOpenEquiv = evaluateClassicalSpecialization(
    eGaps,
    "B_star",
    [aClaim],
    [equiv("B_star", "a", "b")],
  );
  assert.equal(resOpenEquiv.ok, false);

  // 4. Support domainConstraint in UL-Classical forall / exists
  const p = (h: string) => atom("P", [{ role: "arg", handle: h }]);
  const dPred = (h: string) => atom("D_pred", [{ role: "arg", handle: h }]);
  const eDom = new InquiryEngine(b, { monotoneOnly: true });
  eDom.observePositive("B_star", dPred("a"), "w_da");
  eDom.observeNegative("B_star", dPred("b"), "w_ndb");
  eDom.observePositive("B_star", p("a"), "w_pa");
  eDom.observeNegative("B_star", p("b"), "w_npb");

  const constrainedForall = forall("x", "B_star", p("x"), dPred("x"));
  const constrainedExists = exists("x", "B_star", p("x"), flip(dPred("x")));
  const resDom = evaluateClassicalSpecialization(
    eDom,
    "B_star",
    [dPred("a"), dPred("b"), p("a"), p("b")],
    [constrainedForall, constrainedExists],
  );
  assert.equal(resDom.ok, true);
  if (resDom.ok) {
    assert.equal(resDom.results.get(itemKey(constrainedForall))?.polarity, "+");
    assert.equal(resDom.results.get(itemKey(constrainedExists))?.polarity, "-");
  }

  // 5. Priority 2 Cleanup #1: conflict detected on negCollapseEquivalent of the LAST query item q
  const eLastImposs = new InquiryEngine(b, { monotoneOnly: true });
  const qAtom = atom("Q_Last");
  eLastImposs.observeNegative("B_star", qAtom, "w_nq");
  eLastImposs.observeNegative("B_star", implies(qAtom, bottom()), "w_nimp_bot");
  const resLastConflict = evaluateClassicalSpecialization(
    eLastImposs,
    "B_star",
    [qAtom],
    [qAtom],
  );
  assert.equal(resLastConflict.ok, false);
}

test("four-tier deductive spectrum and classical recovery", test_four_tier_deductive_spectrum_and_classical_recovery);
test(
  "classical atomic cover 2^k Boolean algebra reporting",
  test_classical_atomic_cover_2k_boolean_algebra_reporting,
);
test(
  "classical specialization guards compound exclusions No-Gaps and frozen constraints",
  test_classical_specialization_guards_compound_exclusions_nogaps_and_frozen,
);
