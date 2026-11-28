import assert from "node:assert/strict";
import { test } from "node:test";
import { BOT_BOUNDARY, BoundarySystem } from "../src/boundary.ts";
import { InquiryEngine } from "../src/engine.ts";
import {
  evaluateClassicalSpecialization,
  verifyIntuitionisticSpecialization,
  verifyMinimalSpecialization,
} from "../src/specializations.ts";
import { and, atom, bottom, equiv, exists, flip, forall, implies, itemKey, or, type Item } from "../src/syntax.ts";

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
  assert.equal(eCov.evaluate([lemItem]).localStatus("B", lemItem), "Grounded");

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
  assert.equal(coreSnap.localStatus("B_star", aImpliesC), "Open");
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

function test_classical_cover_requires_valid_cover_with_known_cell_overlaps(): void {
  const aClaim = atom("A");
  const run = (declareCells: boolean, addUnsettledSub: boolean) => {
    const b = new BoundarySystem();
    b.defineBoundary("B");
    b.defineBoundary("B1_star", { parents: ["B"] });
    b.defineBoundary("B2_star", { parents: ["B"] });
    if (declareCells) {
      b.declareDisjoint("B1_star", "B2_star");
    }
    b.registerCover("B", ["B1_star", "B2_star"]);
    if (addUnsettledSub) {
      b.defineBoundary("B3", { parents: ["B"] });
    }
    const engine = new InquiryEngine(b, { monotoneOnly: true });
    engine.observePositive("B1_star", aClaim, "w_b1_a");
    engine.observeNegative("B2_star", aClaim, "w_b2_na");
    return evaluateClassicalSpecialization(engine, "B", [aClaim], [aClaim]);
  };
  assert.equal(run(true, false).ok, true);

  // (C3): cells whose overlap with one another is unknown do not form a classical cover.
  const unknownCells = run(false, false);
  assert.equal(unknownCells.ok, false);
  if (!unknownCells.ok) {
    assert.match(unknownCells.reason, /known overlaps/);
  }
  // (C3): a cover left unverified by B3 ⊑ B, whose overlap with both cells is unknown, is refused.
  const unverified = run(true, true);
  assert.equal(unverified.ok, false);
  if (!unverified.ok) {
    assert.match(unverified.reason, /unverified/);
  }
}

function test_classical_check_covers_tracked_items_constraints_and_handles(): void {
  // audit-classical-check-completeness (R9): the valuation must agree with every ground and
  // constraint of Σ, every sub-item is checked, and the items name only handles of Dom(B*).
  const run = (setup: (e: InquiryEngine) => void, atoms: readonly Item[], queries: readonly Item[]) => {
    const b = new BoundarySystem();
    b.defineBoundary("Bs", { nativeRelations: ["H"], handles: [{ id: "k", criterion: "I", kind: "structural" }] });
    const e = new InquiryEngine(b, { monotoneOnly: true });
    setup(e);
    return evaluateClassicalSpecialization(e, "Bs", atoms, queries);
  };
  const P = atom("P");
  const Q = atom("Q");
  const A = atom("A");
  const B = atom("B");
  const C = atom("C");
  const refused = (res: ReturnType<typeof run>, pattern: RegExp): void => {
    assert.equal(res.ok, false);
    if (!res.ok) {
      assert.match(res.reason, pattern);
    }
  };
  // (a) A tracked compound outside the queries.
  refused(run((e) => {
    e.observeNegative("Bs", P, "np");
    e.observeNegative("Bs", Q, "nq");
    e.observePositive("Bs", implies(implies(P, Q), P), "w");
  }, [P, Q], [implies(P, Q)]), /conflicts with existing "Grounded"/);
  // (b) A registered incompatibility.
  refused(run((e) => {
    e.observeNegative("Bs", P, "np");
    e.observeNegative("Bs", Q, "nq");
    e.addIncompatibility("Bs", implies(P, Q), implies(Q, P));
  }, [P, Q], [implies(P, Q)]), /both sides of the incompatibility/);
  // (c) A conflict on a sub-item that a short-circuit used to skip.
  refused(run((e) => {
    e.observeNegative("Bs", A, "na");
    e.observeNegative("Bs", B, "nb");
    e.observeNegative("Bs", C, "nc");
    e.observeNegative("Bs", implies(B, C), "nbc");
  }, [A, B, C], [and(A, implies(B, C))]), /conflicts with existing "Excluded"/);
  // (d) A handle outside Dom(B*).
  const outside = atom("H", [{ role: "arg", handle: "zzz" }]);
  refused(run(() => undefined, [outside], [outside]), /\(C3\) requires the items to name only handles/);
  // A consistent state still evaluates.
  const ok = run((e) => {
    e.observeNegative("Bs", P, "np");
    e.observePositive("Bs", Q, "q");
  }, [P, Q], [implies(P, Q)]);
  assert.equal(ok.ok, true);
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
  eDom.closeDomain("B_star");

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

function test_classical_specialization_requires_closed_nonempty_domains(): void {
  const h = (id: string) => ({ id, criterion: `I(${id})`, kind: "structural" as const });
  const b = new BoundarySystem();
  b.defineBoundary("Universe", { nativeRelations: ["P"], handles: [h("a"), h("b"), h("c")] });
  b.defineBoundary("B_star", { parents: ["Universe"], handles: [h("a"), h("b")] });
  b.defineBoundary("Empty", { handles: [] });
  const p = (x: string) => atom("P", [{ role: "arg", handle: x }]);
  const atoms = [p("a"), p("b")];
  const e = new InquiryEngine(b, { monotoneOnly: true });
  e.observePositive("B_star", p("a"), "w_pa");
  e.observeNegative("B_star", p("b"), "w_npb");

  // (C3): a quantifier domain without a witnessed CloseDomain is rejected.
  const allStar = forall("x", "B_star", p("x"));
  const exStar = exists("x", "B_star", p("x"));
  const unclosed = evaluateClassicalSpecialization(e, "B_star", atoms, [allStar, exStar]);
  assert.equal(unclosed.ok, false);
  if (!unclosed.ok) {
    assert.match(unclosed.reason, /CloseDomain\("B_star"\)/);
  }

  // Closed, non-empty and inside Dom(B*): classical values follow.
  e.closeDomain("B_star");
  const closed = evaluateClassicalSpecialization(e, "B_star", atoms, [allStar, exStar]);
  assert.equal(closed.ok, true);
  if (closed.ok) {
    assert.equal(closed.results.get(itemKey(allStar))?.polarity, "-");
    assert.equal(closed.results.get(itemKey(exStar))?.polarity, "+");
  }

  // A closed but empty domain is rejected, also when nested inside another quantifier.
  e.closeDomain("Empty");
  const empty = evaluateClassicalSpecialization(e, "B_star", atoms, [forall("x", "Empty", p("x"))]);
  assert.equal(empty.ok, false);
  if (!empty.ok) {
    assert.match(empty.reason, /non-empty quantifier domains; Dom\("Empty"\) is empty/);
  }
  const nested = evaluateClassicalSpecialization(e, "B_star", atoms, [
    forall("x", "B_star", exists("y", "Empty", p("y"))),
  ]);
  assert.equal(nested.ok, false);

  // A closed domain reaching beyond Dom(B*) is rejected.
  e.closeDomain("Universe");
  const wide = evaluateClassicalSpecialization(e, "B_star", atoms, [forall("x", "Universe", p("x"))]);
  assert.equal(wide.ok, false);
  if (!wide.ok) {
    assert.match(wide.reason, /Dom\("Universe"\) ⊆ Dom\("B_star"\); handle "c"/);
  }

  // ⊥_B can never be closed, so a quantifier over it never meets (C3).
  const overBottom = evaluateClassicalSpecialization(e, "B_star", atoms, [forall("x", BOT_BOUNDARY, p("x"))]);
  assert.equal(overBottom.ok, false);
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
test(
  "classical specialization requires closed non-empty domains",
  test_classical_specialization_requires_closed_nonempty_domains,
);
test("classical cover requires a valid cover with known cell overlaps", test_classical_cover_requires_valid_cover_with_known_cell_overlaps);
test("classical check covers tracked items, constraints and handles", test_classical_check_covers_tracked_items_constraints_and_handles);
