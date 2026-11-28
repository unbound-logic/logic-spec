import assert from "node:assert/strict";
import { test } from "node:test";
import { BoundarySystem } from "../src/boundary.ts";
import { verifyDerivation } from "../src/deduction.ts";
import { InquiryEngine } from "../src/engine.ts";
import { atom, forall, implies, ref, refl, reflStatus } from "../src/syntax.ts";

function test_reflection_values_and_formal_layer_syntax(): void {
  // audit-reflection-authority-flattening (R13): a stage-indexed reflection takes + for a Live
  // record, - for a Quarantined or absent one, and no value for an Undetermined one.
  const b = new BoundarySystem();
  b.defineBoundary("B");
  b.defineBoundary("B_sub", { parents: ["B"] });
  const e = new InquiryEngine(b);
  const [P, Q, R, X] = [atom("P"), atom("Q"), atom("R"), atom("X")];
  e.observePositive("B", P, "wp");
  e.observePositive("B", Q, "wq");
  e.addIncompatibility("B", P, Q); // symmetric conflict: +P is Undetermined
  e.observePositive("B", R, "wr");
  e.observeNegative("B_sub", R, "wnr"); // the collision on B_sub quarantines +R on B
  e.observePositive("B", X, "wx"); // +X is Live
  const t = e.stage;
  const at = e.evaluateAtStage(t, [P, R, X]);
  assert.equal(at.authorityOf("B", "+", P), "Undetermined");
  assert.equal(at.authorityOf("B", "+", R), "Quarantined");
  assert.equal(at.authorityOf("B", "+", X), "Live");
  e.observePositive("B", atom("Later"), "later");
  const reflections = [refl(1, "B", "+", P, t), refl(1, "B", "+", R, t), refl(1, "B", "+", X, t), refl(1, "B", "-", X, t)];
  const snap = e.evaluate(reflections);
  assert.deepEqual(
    reflections.map((r) => snap.localStatus("B", r)),
    ["Open", "Excluded", "Grounded", "Excluded"],
  );
  // refl-intro refuses to give the undetermined record a value.
  const undetermined = verifyDerivation(e, { kind: "refl-intro", boundary: "B", reflItem: refl(1, "B", "+", P, t) });
  assert.equal(undetermined.ok ? "accepted" : undetermined.violation, "ground-not-live");

  // audit-unexecuted-syntax: a stage-less reflection and a recursive reference belong to the formal
  // layer: they are well-formed items, but evaluation gives them no value, and refl-intro refuses a
  // stage-less reflection.
  const stageless = refl(1, "B", "+", X);
  const recursive = ref("Loop");
  const formal = e.evaluate([stageless, recursive]);
  assert.equal(formal.localStatus("B", stageless), "Open");
  assert.equal(formal.localStatus("B", recursive), "Open");
  const stagelessIntro = verifyDerivation(e, { kind: "refl-intro", boundary: "B", reflItem: stageless });
  assert.equal(stagelessIntro.ok, false);
}

function test_cross_stage_reflection_trace_and_historical_immutability(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  const engine = new InquiryEngine(b);
  const a = atom("A");
  const needAudit = atom("NeedAudit");

  // Build trace: Σ0 (Open) -> Σ1 (+A) -> Σ2 (Collision) -> Σ3 (Retract neg -> +A) -> Σ4 (Retract pos -> Open)
  assert.equal(engine.stage, 0);
  engine.observePositive("B", a, "w_a"); // Σ1
  engine.observeNegative("B", a, "w_na"); // Σ2
  assert.equal(engine.retract("w_na"), true); // Σ3
  assert.equal(engine.retract("w_a"), true); // Σ4
  assert.equal(engine.stage, 4);

  const r0Open = reflStatus(0, 0, "B", a, "Open");
  const r1Grounded = reflStatus(0, 1, "B", a, "Grounded");
  const r1LivePos = refl(0, "B", "+", a, 1);
  const r2Collision = reflStatus(0, 2, "B", a, "Collision");
  const r2LivePos = refl(0, "B", "+", a, 2);
  const r3LivePos = refl(0, "B", "+", a, 3);
  const sameStage = reflStatus(0, 4, "B", a, "Open");

  const snap4 = engine.evaluate([
    r0Open,
    r1Grounded,
    r1LivePos,
    r2Collision,
    r2LivePos,
    r3LivePos,
    sameStage,
  ]);

  assert.equal(snap4.localStatus("B", r0Open), "Grounded");
  assert.equal(snap4.localStatus("B", r1Grounded), "Grounded");
  assert.equal(snap4.localStatus("B", r1LivePos), "Grounded");
  assert.equal(snap4.localStatus("B", r2Collision), "Grounded");
  assert.equal(snap4.localStatus("B", r2LivePos), "Excluded"); // Quarantined at Σ2 -> Live is false
  assert.equal(snap4.localStatus("B", r3LivePos), "Grounded"); // Reinstated at Σ3 -> Live is true
  assert.equal(snap4.localStatus("B", sameStage), "Open"); // Same-stage reflection withheld

  // Meta-reasoning via Scoped Cut: trigger NeedAudit from historical Σ2 collision
  engine.observePositive("B", implies(r2Collision, needAudit), "w_audit"); // Σ5
  const nestedValid = refl(1, "B", "+", r1LivePos, 2); // level 1 reflects level-0 item at Σ2 < Σ5
  const nestedIllLevel = refl(0, "B", "+", r1LivePos, 2); // level 0 < inner level 1 -> Open

  const snap5 = engine.evaluate([needAudit, nestedValid, nestedIllLevel]);
  assert.equal(snap5.localStatus("B", needAudit), "Grounded");
  assert.equal(snap5.isLive("B", "+", needAudit), true);
  assert.equal(snap5.localStatus("B", nestedValid), "Grounded");
  assert.equal(snap5.localStatus("B", nestedIllLevel), "Open");
}

function test_cross_stage_reflection_curry_immunity_and_deduction_stratification(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");

  // Operational worked-examples §3 Vector 2 check: K_1 := Refl_0@Σ0(B ⊩+ K_0) → MoonIsCheese
  const eCurry = new InquiryEngine(b);
  const k0 = atom("K_0");
  const moon = atom("MoonIsCheese");
  const reflK0 = refl(0, "B", "+", k0, 0);
  eCurry.observePositive("B", implies(reflK0, moon), "w_k1"); // Σ1

  const snapCurry = eCurry.evaluate([moon]);
  assert.equal(snapCurry.localStatus("B", reflK0), "Excluded");
  assert.equal(snapCurry.localStatus("B", moon), "Open");

  // Deduction rule refl-intro stratification and polarity checks
  const engine = new InquiryEngine(b);
  const a = atom("A");
  engine.observePositive("B", a, "w_a"); // Σ1: +A Live
  engine.observeNegative("B", a, "w_na"); // Σ2: A Collision (+A un-Live)
  engine.observePositive("B", atom("Step3"), "w_step3"); // Σ3

  const validPos = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: refl(0, "B", "+", a, 1),
  });
  assert.equal(validPos.ok, true);
  if (validPos.ok) {
    assert.equal(validPos.polarity, "+");
  }

  const validQuarantinedNeg = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: refl(0, "B", "+", a, 2),
  });
  assert.equal(validQuarantinedNeg.ok, true);
  if (validQuarantinedNeg.ok) {
    assert.equal(validQuarantinedNeg.polarity, "-");
  }

  const failSameStage = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: refl(0, "B", "+", a, 3),
  });
  assert.equal(failSameStage.ok, false);
  if (!failSameStage.ok) {
    assert.equal(failSameStage.violation, "stratification-violation");
  }

  const failFutureStage = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: refl(0, "B", "+", a, 9),
  });
  assert.equal(failFutureStage.ok, false);
  if (!failFutureStage.ok) {
    assert.equal(failFutureStage.violation, "stratification-violation");
  }

  const failLevel = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: refl(0, "B", "+", refl(0, "B", "+", a, 1), 2),
  });
  assert.equal(failLevel.ok, false);
  if (!failLevel.ok) {
    assert.equal(failLevel.violation, "stratification-violation");
  }
}

function test_stage_archive_isolates_historical_boundary_and_cover_mutations(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  b.defineBoundary("B1", { parents: ["B"] });
  b.defineBoundary("B2", { parents: ["B"] });
  b.declareDisjoint("B1", "B2");

  const engine = new InquiryEngine(b);
  const p = atom("P");
  engine.observePositive("B1", p, "w_b1"); // Σ1
  engine.observePositive("B2", p, "w_b2"); // Σ2 (cover not yet registered)

  // Mutate BoundarySystem after Σ2 by registering cover {B1, B2} ▷ B
  b.registerCover("B", ["B1", "B2"]);
  engine.observePositive("B", atom("Tick"), "w_tick"); // Σ3

  // Historical Σ2 must remain isolated from post-Σ2 registerCover mutation
  assert.equal(engine.evaluateAtStage(2, [p]).localStatus("B", p), "Open");
  // Live evaluation at Σ3 sees the registered cover
  assert.equal(engine.evaluate([p]).localStatus("B", p), "Grounded");

  // Reflection against Σ2 observes historical Open/non-Live rather than retroactively Grounded
  const reflAt2 = refl(0, "B", "+", p, 2);
  assert.equal(engine.evaluate([reflAt2]).localStatus("B", reflAt2), "Excluded");
}

function test_cross_stage_reflection_rejects_post_stage_boundaries(): void {
  // 1. Bug C: Boundaries created AFTER stage t must not be hallucinated or crash evaluation at Σ_t
  const b = new BoundarySystem();
  b.defineBoundary("B", { nativeRelations: ["P"] });
  const engine = new InquiryEngine(b);
  const a = atom("A");
  engine.observePositive("B", a, "w_a"); // Σ1 (B_new does NOT exist yet!)

  b.defineBoundary("B_new", { nativeRelations: ["P"] });
  engine.observePositive("B", atom("Tick"), "w_tick"); // Σ2 (B_new exists in Σ2, not Σ1)

  const reflHalluc = reflStatus(0, 1, "B_new", a, "Open");
  const snapHalluc = engine.evaluate([reflHalluc]);
  assert.equal(snapHalluc.localStatus("B", reflHalluc), "Open");

  const deductHalluc = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: reflHalluc,
  });
  assert.equal(deductHalluc.ok, false);
  if (!deductHalluc.ok) {
    assert.equal(deductHalluc.violation, "invalid-boundary");
  }

  const reflInnerDomain = refl(
    0,
    "B",
    "+",
    forall("x", "B_new", atom("P", [{ role: "arg", handle: "x" }])),
    1,
  );
  const snapNoCrash = engine.evaluate([reflInnerDomain]);
  assert.equal(snapNoCrash.localStatus("B", reflInnerDomain), "Open");

  const deductInnerDomain = verifyDerivation(engine, {
    kind: "refl-intro",
    boundary: "B",
    reflItem: reflInnerDomain,
  });
  assert.equal(deductInnerDomain.ok, false);
  if (!deductInnerDomain.ok) {
    assert.equal(deductInnerDomain.violation, "invalid-boundary");
  }

  // 2. Priority 2 Cleanup #2: witnessCover vertical transition advances stage and isolates history
  const bCov = new BoundarySystem();
  bCov.defineBoundary("B");
  bCov.defineBoundary("B1", { parents: ["B"] });
  bCov.defineBoundary("B2", { parents: ["B"] });
  bCov.declareDisjoint("B1", "B2");
  const eCov = new InquiryEngine(bCov);
  const p = atom("P");
  eCov.observePositive("B1", p, "w_b1"); // Σ1
  eCov.observePositive("B2", p, "w_b2"); // Σ2
  eCov.witnessCover("B", ["B1", "B2"]); // Σ3

  assert.equal(eCov.stage, 3);
  assert.match(eCov.transitionLog[2] ?? "", /WitnessCover/);
  assert.equal(eCov.evaluateAtStage(2, [p]).localStatus("B", p), "Open");
  assert.equal(eCov.evaluate([p]).localStatus("B", p), "Grounded");
  assert.equal(eCov.evaluateAtStage(3, [p]).localStatus("B", p), "Grounded");
}

test("cross-stage reflection trace and historical immutability", test_cross_stage_reflection_trace_and_historical_immutability);
test("cross-stage reflection Curry immunity and deduction stratification", test_cross_stage_reflection_curry_immunity_and_deduction_stratification);
test(
  "stage archive isolates historical boundary and cover mutations",
  test_stage_archive_isolates_historical_boundary_and_cover_mutations,
);
test(
  "cross-stage reflection rejects post-stage boundaries",
  test_cross_stage_reflection_rejects_post_stage_boundaries,
);
test("reflection values and formal-layer syntax", test_reflection_values_and_formal_layer_syntax);
