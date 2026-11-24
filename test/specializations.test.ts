import assert from "node:assert/strict";
import { test } from "node:test";
import { BoundarySystem } from "../src/boundary.ts";
import { InquiryEngine } from "../src/engine.ts";
import {
  evaluateClassicalSpecialization,
  verifyIntuitionisticSpecialization,
  verifyMinimalSpecialization,
} from "../src/specializations.ts";
import { atom, flip, implies, itemKey, or } from "../src/syntax.ts";

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

  const eCov = new InquiryEngine(bCov);
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
  const eAtomic = new InquiryEngine(bAtomic);
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
  const eConflict = new InquiryEngine(bAtomic);
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

test("four-tier deductive spectrum and classical recovery", test_four_tier_deductive_spectrum_and_classical_recovery);
