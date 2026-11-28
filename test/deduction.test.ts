import assert from "node:assert/strict";
import { test } from "node:test";
import { BoundarySystem } from "../src/boundary.ts";
import { admitVerifiedDerivation, verifyDerivation } from "../src/deduction.ts";
import { InquiryEngine } from "../src/engine.ts";
import {
  and,
  atom,
  bottom,
  checkRecursiveDefinitionSystem,
  equiv,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  ref,
  structImposs,
  substituteHandle,
} from "../src/syntax.ts";

function test_eigenvariable_freshness_and_one_position_congruence(): void {
  // audit-deduction-freshness-and-congruence (R8): a handle named only by a retracted observation
  // is still tracked, so it is no fresh eigenvariable ...
  const b = new BoundarySystem();
  b.defineBoundary("D", { nativeRelations: ["R"], handles: [{ id: "t1", criterion: "I", kind: "structural" }] });
  const e = new InquiryEngine(b);
  const r = (x: string) => atom("R", [{ role: "arg", handle: x }]);
  e.observePositive("D", r("ghost"), "wg");
  e.retract("wg");
  const res = verifyDerivation(e, {
    kind: "forall-intro",
    boundary: "D",
    variable: "x",
    domain: "D",
    eigenvar: "ghost",
    templateBody: implies(r("x"), r("x")),
    body: {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "h",
      antecedent: r("ghost"),
      body: { kind: "assume", assumptionId: "h", boundary: "D" },
    },
  });
  assert.equal(res.ok ? "accepted" : res.violation, "eigenvariable-not-fresh");

  // ... and equiv-subst rewrites one position at a time, to a handle of a declared boundary.
  const c = new BoundarySystem();
  c.defineBoundary("E", {
    nativeRelations: ["Rel"],
    handles: [
      { id: "h0", criterion: "I(h0)", kind: "structural" },
      { id: "h1", criterion: "I(h1)", kind: "structural" },
    ],
  });
  const ee = new InquiryEngine(c);
  const rel2 = (x: string, y: string) => atom("Rel", [{ role: "from", handle: x }, { role: "to", handle: y }]);
  ee.observePositive("E", equiv("E", "h0", "h1"), "w_eq");
  ee.observePositive("E", equiv("E", "h0", "nowhere"), "w_eq_free");
  ee.observePositive("E", rel2("h0", "h0"), "w_rel");
  const subst = (equivItem: ReturnType<typeof equiv>, position?: number) =>
    verifyDerivation(ee, {
      kind: "equiv-subst",
      direction: "left-to-right",
      equivProof: { kind: "live-ground", boundary: "E", polarity: "+", item: equivItem },
      targetProof: { kind: "live-ground", boundary: "E", polarity: "+", item: rel2("h0", "h0") },
      ...(position === undefined ? {} : { position }),
    });
  const both = subst(equiv("E", "h0", "h1"));
  assert.equal(both.ok, false); // two occurrences: a position is required
  const first = subst(equiv("E", "h0", "h1"), 0);
  assert.equal(first.ok, true);
  if (first.ok) {
    assert.equal(itemKey(first.item), itemKey(rel2("h1", "h0")));
  }
  assert.equal(subst(equiv("E", "h0", "nowhere"), 0).ok, false); // no declared boundary admits "nowhere"
}

function test_standalone_cover_gluing_and_quarantine_propagation(): void {
  const b = new BoundarySystem();
  b.defineBoundary("Z");
  b.defineBoundary("Even", { parents: ["Z"] });
  b.defineBoundary("Odd", { parents: ["Z"] });
  b.declareDisjoint("Even", "Odd");
  b.registerCover("Z", ["Even", "Odd"]);

  const engine = new InquiryEngine(b);
  const p = atom("GluedPos");
  const q = atom("GluedNeg");
  const r = atom("IncompleteCell");

  engine.observePositive("Even", p, "w_ep");
  engine.observePositive("Odd", p, "w_op");
  engine.observeNegative("Even", q, "w_eq");
  engine.observeNegative("Odd", q, "w_oq");
  engine.observePositive("Even", r, "w_er");

  // Standalone engine Cover-Gluing glues both polarities on complete cover and skips incomplete cover
  const snap0 = engine.evaluate([p, q, r]);
  assert.equal(snap0.localStatus("Z", p), "Grounded");
  assert.equal(snap0.isLive("Z", "+", p), true);
  assert.equal(snap0.localStatus("Z", q), "Excluded");
  assert.equal(snap0.isLive("Z", "-", q), true);
  assert.equal(snap0.localStatus("Z", r), "Open");

  // Natural deduction cover-glue rule succeeds on witnessed cover and rejects incomplete cover
  const gluedProof = verifyDerivation(engine, {
    kind: "cover-glue",
    boundary: "Z",
    item: p,
    cellProofs: [
      { cell: "Even", proof: { kind: "live-ground", boundary: "Even", polarity: "+", item: p } },
      { cell: "Odd", proof: { kind: "live-ground", boundary: "Odd", polarity: "+", item: p } },
    ],
  });
  assert.equal(gluedProof.ok, true);
  if (gluedProof.ok) {
    assert.equal(gluedProof.boundary, "Z");
    assert.equal(gluedProof.polarity, "+");
    assert.deepEqual(gluedProof.requiredBaseIds, ["w_ep", "w_op"]);
  }

  const badCoverProof = verifyDerivation(engine, {
    kind: "cover-glue",
    boundary: "Z",
    item: r,
    cellProofs: [
      { cell: "Even", proof: { kind: "live-ground", boundary: "Even", polarity: "+", item: r } },
    ],
  });
  assert.equal(badCoverProof.ok, false);
  if (!badCoverProof.ok) {
    assert.equal(badCoverProof.violation, "unwitnessed-cover");
  }

  // Admit the verified cover-glue theorem onto Z on a clone/second run, then collide Odd:
  const b2 = new BoundarySystem();
  b2.defineBoundary("Z");
  b2.defineBoundary("Even", { parents: ["Z"] });
  b2.defineBoundary("Odd", { parents: ["Z"] });
  b2.declareDisjoint("Even", "Odd");
  b2.registerCover("Z", ["Even", "Odd"]);
  const eAdmit = new InquiryEngine(b2);
  eAdmit.observePositive("Even", p, "w_ep");
  eAdmit.observePositive("Odd", p, "w_op");
  const admitCov = admitVerifiedDerivation(
    eAdmit,
    {
      kind: "cover-glue",
      boundary: "Z",
      item: p,
      cellProofs: [
        { cell: "Even", proof: { kind: "live-ground", boundary: "Even", polarity: "+", item: p } },
        { cell: "Odd", proof: { kind: "live-ground", boundary: "Odd", polarity: "+", item: p } },
      ],
    },
    "thm_glued_p",
  );
  assert.equal(admitCov.ok, true);
  assert.equal(eAdmit.evaluate([p]).isLive("Z", "+", p), true);
  eAdmit.observeNegative("Odd", p, "w_odd_refute");
  const snapAdmitColl = eAdmit.evaluate([p]);
  assert.equal(snapAdmitColl.localStatus("Odd", p), "Collision");
  assert.equal(snapAdmitColl.isObstructed("Z", p), true);
  assert.equal(snapAdmitColl.isLive("Z", "+", p), false);

  // Without an explicit entry on Z, colliding one cover cell suppresses Rule I gluing cleanly (no ghost Z ⊩+ P)
  engine.observeNegative("Odd", p, "w_odd_refute");
  const snapColl = engine.evaluate([p]);
  assert.equal(snapColl.localStatus("Odd", p), "Collision");
  assert.equal(snapColl.localStatus("Z", p), "Open");
  assert.equal(snapColl.allGrounds("Z", "+", p).length, 0);
  assert.equal(snapColl.isLive("Z", "+", p), false);
}

function test_natural_deduction_implies_intro_and_anti_vacuity_quarantine(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  const engine = new InquiryEngine(b);

  const a = atom("A");
  const bItem = atom("B_item");
  const c = atom("C");

  // Combinators I: A → A, K: A → (C → A), S: (A → (B → C)) → ((A → B) → (A → C))
  const idProof = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "B",
    assumptionId: "hA",
    antecedent: a,
    body: { kind: "assume", assumptionId: "hA", boundary: "B" },
  });
  assert.equal(idProof.ok, true);
  if (idProof.ok) {
    assert.equal(itemKey(idProof.item), itemKey(implies(a, a)));
  }

  const kProof = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "B",
    assumptionId: "hA",
    antecedent: a,
    body: {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "hC",
      antecedent: c,
      body: { kind: "assume", assumptionId: "hA", boundary: "B" },
    },
  });
  assert.equal(kProof.ok, true);
  if (kProof.ok) {
    assert.equal(itemKey(kProof.item), itemKey(implies(a, implies(c, a))));
  }

  const aToBC = implies(a, implies(bItem, c));
  const aToB = implies(a, bItem);
  const sProof = verifyDerivation(
    engine,
    {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "hABC",
      antecedent: aToBC,
      body: {
        kind: "implies-intro",
        boundary: "B",
        assumptionId: "hAB",
        antecedent: aToB,
        body: {
          kind: "implies-intro",
          boundary: "B",
          assumptionId: "hA",
          antecedent: a,
          body: {
            kind: "implies-elim",
            premise: {
              kind: "implies-elim",
              premise: { kind: "assume", assumptionId: "hA", boundary: "B" },
              conditional: { kind: "assume", assumptionId: "hAB", boundary: "B" },
            },
            conditional: {
              kind: "implies-elim",
              premise: { kind: "assume", assumptionId: "hA", boundary: "B" },
              conditional: { kind: "assume", assumptionId: "hABC", boundary: "B" },
            },
          },
        },
      },
    },
    "UL-Core",
  );
  assert.equal(sProof.ok, true);

  // Anti-vacuity: -A alone must NOT fabricate A → C in UL-Core
  engine.observeNegative("B", a, "w_neg_a");
  const badVacuous = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "B",
    assumptionId: "hA",
    antecedent: a,
    body: { kind: "live-ground", boundary: "B", polarity: "+", item: implies(a, c) },
  });
  assert.equal(badVacuous.ok, false);
  if (!badVacuous.ok) {
    assert.equal(badVacuous.violation, "ground-not-live");
  }

  const badExFalsoCore = verifyDerivation(
    engine,
    {
      kind: "ex-falso-bottom",
      bottomProof: { kind: "live-ground", boundary: "B", polarity: "+", item: bottom() },
      target: c,
    },
    "UL-Core",
  );
  assert.equal(badExFalsoCore.ok, false);
  if (!badExFalsoCore.ok) {
    assert.equal(badExFalsoCore.violation, "ex-falso-disallowed");
  }

  // Curry firewall blocks K := K → Z at syntax level
  const curryAttempt = checkRecursiveDefinitionSystem([
    { name: "K", level: 0, body: implies(ref("K"), atom("MoonIsCheese")) },
  ]);
  assert.equal(curryAttempt.ok, false);

  // Provenance & Quarantine bridge: admit B ⊩+ (A → C) anchored to w_c, then collide and retract w_c
  engine.observePositive("B", c, "w_c");
  const admitted = admitVerifiedDerivation(
    engine,
    {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "hA",
      antecedent: a,
      body: { kind: "live-ground", boundary: "B", polarity: "+", item: c },
    },
    "thm_ac",
  );
  assert.equal(admitted.ok, true);
  assert.equal(engine.evaluate().isLive("B", "+", implies(a, c)), true);

  // Colliding C removes Live authority from admitted theorem B ⊩+ (A → C)
  engine.observeNegative("B", c, "w_nc");
  const snapColl = engine.evaluate();
  assert.equal(snapColl.localStatus("B", c), "Collision");
  assert.equal(snapColl.isLive("B", "+", implies(a, c)), false);

  // Retracting w_c cleanly withdraws the admitted theorem back to Open (zero ghost theorem)
  assert.equal(engine.retract("w_c"), true);
  const snapRetract = engine.evaluate([implies(a, c)]);
  assert.equal(snapRetract.localStatus("B", implies(a, c)), "Open");
}

function test_schematic_forall_intro_eigenvariable_soundness_on_open_domains(): void {
  const b = new BoundarySystem();
  // Open domain D has ZERO pre-registered handles!
  b.defineBoundary("D", { nativeRelations: ["P", "Q", "White"] });
  b.defineBoundary("Ctx", { handles: [{ id: "known_h", criterion: "I(h)", kind: "structural" }] });

  const engine = new InquiryEngine(b);
  const p = (h: string) => atom("P", [{ role: "arg", handle: h }]);
  const q = (h: string) => atom("Q", [{ role: "arg", handle: h }]);
  const white = (h: string) => atom("White", [{ role: "subject", handle: h }]);

  // 1. ∀(x : D) (P(x) → P(x)) over open domain D
  const reflUniv = verifyDerivation(engine, {
    kind: "forall-intro",
    boundary: "D",
    variable: "x",
    domain: "D",
    eigenvar: "α",
    templateBody: implies(p("x"), p("x")),
    body: {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "hP",
      antecedent: p("α"),
      body: { kind: "assume", assumptionId: "hP", boundary: "D" },
    },
  });
  assert.equal(reflUniv.ok, true);
  if (reflUniv.ok) {
    assert.equal(itemKey(reflUniv.item), itemKey(forall("x", "D", implies(p("x"), p("x")))));
  }

  // 2. Universal distribution: (∀(x:D)(P(x) → Q(x))) → ((∀(x:D) P(x)) → (∀(x:D) Q(x)))
  const univDist = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hAllPQ",
    antecedent: forall("x", "D", implies(p("x"), q("x"))),
    body: {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "hAllP",
      antecedent: forall("x", "D", p("x")),
      body: {
        kind: "forall-intro",
        boundary: "D",
        variable: "x",
        domain: "D",
        eigenvar: "β",
        templateBody: q("x"),
        body: {
          kind: "implies-elim",
          premise: {
            kind: "forall-elim",
            universal: { kind: "assume", assumptionId: "hAllP", boundary: "D" },
            term: "β",
          },
          conditional: {
            kind: "forall-elim",
            universal: { kind: "assume", assumptionId: "hAllPQ", boundary: "D" },
            term: "β",
          },
        },
      },
    },
  });
  assert.equal(univDist.ok, true);

  // 3. Existential elimination: (∃(x:D)(P(x) ∧ Q(x))) → (∃(x:D) Q(x))
  const exElim = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hExPQ",
    antecedent: exists("x", "D", and(p("x"), q("x"))),
    body: {
      kind: "exists-elim",
      existential: { kind: "assume", assumptionId: "hExPQ", boundary: "D" },
      witnessVar: "γ",
      assumptionId: "hPQ",
      body: {
        kind: "exists-intro",
        witnessTerm: "γ",
        variable: "x",
        domain: "D",
        templateBody: q("x"),
        witnessProof: {
          kind: "and-elim",
          pair: { kind: "assume", assumptionId: "hPQ", boundary: "D" },
          side: "right",
        },
      },
    },
  });
  assert.equal(exElim.ok, true);

  // 4. Eigenvariable escape & freshness adversarial tests (all must be rejected!)
  engine.observePositive("D", white("swan_1"), "w_swan");

  // 4a) Reusing handle mentioned in Σ (swan_1)
  const badSigmaReuse = verifyDerivation(engine, {
    kind: "forall-intro",
    boundary: "D",
    variable: "x",
    domain: "D",
    eigenvar: "swan_1",
    templateBody: white("x"),
    body: { kind: "live-ground", boundary: "D", polarity: "+", item: white("swan_1") },
  });
  assert.equal(badSigmaReuse.ok, false);
  if (!badSigmaReuse.ok) {
    assert.equal(badSigmaReuse.violation, "eigenvariable-not-fresh");
  }

  // 4b) Reusing handle registered in boundary system (known_h)
  const badBoundReuse = verifyDerivation(engine, {
    kind: "forall-intro",
    boundary: "D",
    variable: "x",
    domain: "D",
    eigenvar: "known_h",
    templateBody: implies(p("x"), p("x")),
    body: {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "hP",
      antecedent: p("known_h"),
      body: { kind: "assume", assumptionId: "hP", boundary: "D" },
    },
  });
  assert.equal(badBoundReuse.ok, false);
  if (!badBoundReuse.ok) {
    assert.equal(badBoundReuse.violation, "eigenvariable-not-fresh");
  }

  // 4c) Leaking eigenvariable into open outer assumption: White(α) → ∀(x:D) White(x)
  const badOuterAssump = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hWhiteAlpha",
    antecedent: white("α"),
    body: {
      kind: "forall-intro",
      boundary: "D",
      variable: "x",
      domain: "D",
      eigenvar: "α",
      templateBody: white("x"),
      body: { kind: "assume", assumptionId: "hWhiteAlpha", boundary: "D" },
    },
  });
  assert.equal(badOuterAssump.ok, false);
  if (!badOuterAssump.ok) {
    assert.equal(badOuterAssump.violation, "eigenvariable-not-fresh");
  }

  // 4d) Escaping ∃E witness variable into conclusion E
  const badExistsEscape = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hEx",
    antecedent: exists("x", "D", q("x")),
    body: {
      kind: "exists-elim",
      existential: { kind: "assume", assumptionId: "hEx", boundary: "D" },
      witnessVar: "δ",
      assumptionId: "hQ",
      body: { kind: "assume", assumptionId: "hQ", boundary: "D" },
    },
  });
  assert.equal(badExistsEscape.ok, false);
  if (!badExistsEscape.ok) {
    assert.equal(badExistsEscape.violation, "eigenvariable-escape");
  }
}

function test_ul_minimal_vs_ul_intuitionistic_proof_theoretic_separation(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  const eMin = new InquiryEngine(b, { monotoneOnly: true });

  const a = atom("A");
  const bItem = atom("B_item");
  const c = atom("C");

  // 1. UL-Minimal proves contraposition (A → B) → ((B → ⊥) → (A → ⊥))
  const contraposition = verifyDerivation(
    eMin,
    {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "hAB",
      antecedent: implies(a, bItem),
      body: {
        kind: "implies-intro",
        boundary: "B",
        assumptionId: "hNotB",
        antecedent: structImposs(bItem),
        body: {
          kind: "implies-intro",
          boundary: "B",
          assumptionId: "hA",
          antecedent: a,
          body: {
            kind: "implies-elim",
            premise: {
              kind: "implies-elim",
              premise: { kind: "assume", assumptionId: "hA", boundary: "B" },
              conditional: { kind: "assume", assumptionId: "hAB", boundary: "B" },
            },
            conditional: { kind: "assume", assumptionId: "hNotB", boundary: "B" },
          },
        },
      },
    },
    "UL-Minimal",
  );
  assert.equal(contraposition.ok, true);

  // 2. UL-Minimal proves (A ∧ (A → ⊥)) → ⊥, yet strictly rejects ⊥ → C and (A ∧ (A → ⊥)) → C
  const minAbsurd = verifyDerivation(
    eMin,
    {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "hPair",
      antecedent: and(a, structImposs(a)),
      body: {
        kind: "implies-elim",
        premise: {
          kind: "and-elim",
          pair: { kind: "assume", assumptionId: "hPair", boundary: "B" },
          side: "left",
        },
        conditional: {
          kind: "and-elim",
          pair: { kind: "assume", assumptionId: "hPair", boundary: "B" },
          side: "right",
        },
      },
    },
    "UL-Minimal",
  );
  assert.equal(minAbsurd.ok, true);

  const botToCProof = {
    kind: "implies-intro" as const,
    boundary: "B",
    assumptionId: "hBot",
    antecedent: bottom(),
    body: {
      kind: "ex-falso-bottom" as const,
      bottomProof: { kind: "assume" as const, assumptionId: "hBot", boundary: "B" },
      target: c,
    },
  };
  const exFalsoContraProof = {
    kind: "implies-intro" as const,
    boundary: "B",
    assumptionId: "hPair",
    antecedent: and(a, structImposs(a)),
    body: {
      kind: "ex-falso-bottom" as const,
      bottomProof: {
        kind: "implies-elim" as const,
        premise: {
          kind: "and-elim" as const,
          pair: { kind: "assume" as const, assumptionId: "hPair", boundary: "B" },
          side: "left" as const,
        },
        conditional: {
          kind: "and-elim" as const,
          pair: { kind: "assume" as const, assumptionId: "hPair", boundary: "B" },
          side: "right" as const,
        },
      },
      target: c,
    },
  };

  const minRejectBot = verifyDerivation(eMin, botToCProof, "UL-Minimal");
  assert.equal(minRejectBot.ok, false);
  if (!minRejectBot.ok) {
    assert.equal(minRejectBot.violation, "ex-falso-disallowed");
  }

  const minRejectContra = verifyDerivation(eMin, exFalsoContraProof, "UL-Minimal");
  assert.equal(minRejectContra.ok, false);
  if (!minRejectContra.ok) {
    assert.equal(minRejectContra.violation, "ex-falso-disallowed");
  }

  // 3. UL-Intuitionistic admits both ⊥ → C and (A ∧ (A → ⊥)) → C cleanly
  const intBot = admitVerifiedDerivation(eMin, botToCProof, "thm_efq", "UL-Intuitionistic");
  assert.equal(intBot.ok, true);
  assert.equal(eMin.evaluate().isLive("B", "+", implies(bottom(), c)), true);

  const intContra = verifyDerivation(eMin, exFalsoContraProof, "UL-Intuitionistic");
  assert.equal(intContra.ok, true);

  // 4. Mode preconditions: UL-Intuitionistic rejects non-monotone engine or Collision
  const eNonMon = new InquiryEngine(b, { monotoneOnly: false });
  const failMon = verifyDerivation(eNonMon, botToCProof, "UL-Intuitionistic");
  assert.equal(failMon.ok, false);
  if (!failMon.ok) {
    assert.equal(failMon.violation, "mode-precondition");
  }

  const eColl = new InquiryEngine(b, { monotoneOnly: true });
  eColl.observePositive("B", a, "wa_pos");
  eColl.observeNegative("B", a, "wa_neg");
  const failColl = verifyDerivation(eColl, botToCProof, "UL-Intuitionistic");
  assert.equal(failColl.ok, false);
  if (!failColl.ok) {
    assert.equal(failColl.violation, "mode-precondition");
  }
}

function test_capture_avoiding_substitution_and_quantifier_bound_variable_freshness(): void {
  const b = new BoundarySystem();
  b.defineBoundary("D", { nativeRelations: ["R"] });
  const engine = new InquiryEngine(b);
  const relR = (a: string, c: string) =>
    atom("R", [
      { role: "a", handle: a },
      { role: "b", handle: c },
    ]);

  // 1A: Reject zero-premise variable-capture proof of ∀(x : D) ∀(α : D) (x ≈_D α)
  const badCaptureProof = verifyDerivation(engine, {
    kind: "forall-intro",
    boundary: "D",
    variable: "x",
    domain: "D",
    eigenvar: "α",
    templateBody: forall("α", "D", equiv("D", "x", "α")),
    body: {
      kind: "forall-intro",
      boundary: "D",
      variable: "α",
      domain: "D",
      eigenvar: "β",
      templateBody: equiv("D", "α", "α"),
      body: { kind: "equiv-refl", boundary: "D", term: "β" },
    },
  });
  assert.equal(badCaptureProof.ok, false);
  if (!badCaptureProof.ok) {
    assert.equal(badCaptureProof.violation, "eigenvariable-not-fresh");
  }

  // 1B: Capture-avoiding substituteHandle and forall-elim rename colliding inner binder "y"
  const nestedExists = exists("y", "D", relR("x", "y"));
  const sub = substituteHandle(nestedExists, "x", "y");
  assert.equal(sub.kind, "exists");
  if (sub.kind === "exists") {
    assert.notEqual(sub.variable, "y");
    assert.equal(itemKey(sub.body), itemKey(relR("y", sub.variable)));
  }

  const bHandles = new BoundarySystem();
  bHandles.defineBoundary("D", {
    nativeRelations: ["R"],
    handles: [{ id: "y", criterion: "I_D(y)", kind: "structural" }],
  });
  const eHandles = new InquiryEngine(bHandles);
  const allEx = forall("x", "D", exists("y", "D", relR("x", "y")));
  const elimCaptureSafe = verifyDerivation(eHandles, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hAll",
    antecedent: allEx,
    body: {
      kind: "forall-elim",
      universal: { kind: "assume", assumptionId: "hAll", boundary: "D" },
      term: "y",
    },
  });
  assert.equal(elimCaptureSafe.ok, true);
  if (elimCaptureSafe.ok && elimCaptureSafe.item.kind === "implies") {
    const con = elimCaptureSafe.item.consequent;
    assert.equal(con.kind, "exists");
    if (con.kind === "exists") {
      assert.notEqual(con.variable, "y");
      assert.equal(itemKey(con.body), itemKey(relR("y", con.variable)));
    }
  }

  // 1C: Reject exists-elim witnessVar colliding with inner bound variable and reject captured exists-intro
  const badExElim = verifyDerivation(engine, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hEx",
    antecedent: exists("x", "D", exists("γ", "D", relR("x", "γ"))),
    body: {
      kind: "exists-elim",
      existential: { kind: "assume", assumptionId: "hEx", boundary: "D" },
      witnessVar: "γ",
      assumptionId: "hBody",
      body: { kind: "assume", assumptionId: "hBody", boundary: "D" },
    },
  });
  assert.equal(badExElim.ok, false);
  if (!badExElim.ok) {
    assert.equal(badExElim.violation, "eigenvariable-not-fresh");
  }

  const badExIntroCapture = verifyDerivation(eHandles, {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "hCap",
    antecedent: exists("y", "D", relR("y", "y")),
    body: {
      kind: "exists-intro",
      witnessTerm: "y",
      variable: "x",
      domain: "D",
      templateBody: exists("y", "D", relR("x", "y")),
      witnessProof: { kind: "assume", assumptionId: "hCap", boundary: "D" },
    },
  });
  assert.equal(badExIntroCapture.ok, false);
  if (!badExIntroCapture.ok) {
    assert.equal(badExIntroCapture.violation, "type-mismatch");
  }
}

function test_admitted_theorem_incompat_persistence_and_intermediate_quarantine(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");

  // 3A: Theorem depending on material incompatibility A ⊥_B C must persist and be Live
  const e3A = new InquiryEngine(b);
  const a = atom("A");
  const c = atom("C");
  e3A.addIncompatibility("B", a, c);
  e3A.observePositive("B", a, "wa");

  const admitIncompat = admitVerifiedDerivation(
    e3A,
    {
      kind: "flip-intro",
      inner: { kind: "live-ground", boundary: "B", polarity: "-", item: c },
    },
    "thm_flip_c",
  );
  assert.equal(admitIncompat.ok, true);
  assert.equal(e3A.evaluate().isLive("B", "+", flip(c)), true);
  assert.equal(e3A.evaluate().localStatus("B", flip(c)), "Grounded");

  assert.equal(e3A.retract("wa"), true);
  assert.equal(e3A.evaluate([flip(c)]).localStatus("B", flip(c)), "Open");

  // 3B: Theorem relying on derived intermediate +(P ∧ Q) must be quarantined when (B, P ∧ Q) collides
  const e3B = new InquiryEngine(b);
  const p = atom("P");
  const q = atom("Q");
  const r = atom("R");
  const pAndQ = and(p, q);
  e3B.observePositive("B", p, "wp");
  e3B.observePositive("B", q, "wq");

  const admitInterm = admitVerifiedDerivation(
    e3B,
    {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "hR",
      antecedent: r,
      body: { kind: "live-ground", boundary: "B", polarity: "+", item: pAndQ },
    },
    "thm_r_pq",
  );
  assert.equal(admitInterm.ok, true);
  assert.equal(e3B.evaluate().isLive("B", "+", implies(r, pAndQ)), true);

  e3B.observeNegative("B", pAndQ, "wnpq");
  const snapColl = e3B.evaluate();
  assert.equal(snapColl.localStatus("B", pAndQ), "Collision");
  assert.equal(snapColl.isLive("B", "+", implies(r, pAndQ)), false);

  assert.equal(e3B.retract("wnpq"), true);
  assert.equal(e3B.evaluate().isLive("B", "+", implies(r, pAndQ)), true);
}

function test_glivenko_double_imposs_does_not_derive_lem_or_dne(): void {
  const b = new BoundarySystem();
  b.defineBoundary("B");
  const eMin = new InquiryEngine(b, { monotoneOnly: true });

  const p = atom("P_Open");
  const lemP = or(p, structImposs(p));
  const negLemP = structImposs(lemP);
  const glivenkoFormula = structImposs(negLemP);

  // Zero-premise minimal-logic derivation of (((P ∨ (P → ⊥)) → ⊥) → ⊥)
  const glivenkoProof = {
    kind: "implies-intro" as const,
    boundary: "B",
    assumptionId: "hNegLem",
    antecedent: negLemP,
    body: {
      kind: "implies-elim" as const,
      conditional: { kind: "assume" as const, assumptionId: "hNegLem", boundary: "B" },
      premise: {
        kind: "or-intro" as const,
        side: "right" as const,
        other: p,
        witness: {
          kind: "implies-intro" as const,
          boundary: "B",
          assumptionId: "hP",
          antecedent: p,
          body: {
            kind: "implies-elim" as const,
            conditional: { kind: "assume" as const, assumptionId: "hNegLem", boundary: "B" },
            premise: {
              kind: "or-intro" as const,
              side: "left" as const,
              other: structImposs(p),
              witness: { kind: "assume" as const, assumptionId: "hP", boundary: "B" },
            },
          },
        },
      },
    },
  };

  assert.equal(verifyDerivation(eMin, glivenkoProof, "UL-Core").ok, true);
  const admitted = admitVerifiedDerivation(eMin, glivenkoProof, "thm_glivenko", "UL-Minimal");
  assert.equal(admitted.ok, true);
  if (admitted.ok) {
    assert.equal(itemKey(admitted.item), itemKey(glivenkoFormula));
  }

  // imposs-excl derives -(lemP → ⊥), yet must NOT invert into +(P ∨ (P → ⊥)) or +P!
  const snap = eMin.evaluate([p, lemP, negLemP, glivenkoFormula]);
  assert.equal(snap.localStatus("B", glivenkoFormula), "Grounded");
  assert.equal(snap.localStatus("B", negLemP), "Excluded");
  assert.equal(snap.localStatus("B", lemP), "Open");
  assert.equal(snap.allGrounds("B", "+", lemP).length, 0);
  assert.equal(snap.localStatus("B", p), "Open");
  assert.equal(snap.allGrounds("B", "+", p).length, 0);
}

test("standalone Cover-Gluing and Quarantine propagation", test_standalone_cover_gluing_and_quarantine_propagation);
test("natural deduction implies-intro, anti-vacuity, and Quarantine bridge", test_natural_deduction_implies_intro_and_anti_vacuity_quarantine);
test("schematic forall-intro and exists-elim eigenvariable soundness on open domains", test_schematic_forall_intro_eigenvariable_soundness_on_open_domains);
test("UL-Minimal vs UL-Intuitionistic proof-theoretic separation", test_ul_minimal_vs_ul_intuitionistic_proof_theoretic_separation);
test(
  "capture-avoiding substitution and quantifier bound variable freshness",
  test_capture_avoiding_substitution_and_quantifier_bound_variable_freshness,
);
test(
  "admitted theorem incompat persistence and intermediate quarantine",
  test_admitted_theorem_incompat_persistence_and_intermediate_quarantine,
);
test(
  "Glivenko double impossibility does not derive LEM or DNE",
  test_glivenko_double_imposs_does_not_derive_lem_or_dne,
);

function test_deduction_quantifier_domain_constraint_enforcement(): void {
  const b = new BoundarySystem();
  b.defineBoundary("R", {
    nativeRelations: ["AddId", "Invertible"],
    handles: [
      { id: "0", criterion: "I_R(0)", kind: "structural" },
      { id: "2", criterion: "I_R(2)", kind: "structural" },
    ],
  });
  const e = new InquiryEngine(b);
  const addId = (h: string) => atom("AddId", [{ role: "el", handle: h }]);
  const inv = (h: string) => atom("Invertible", [{ role: "el", handle: h }]);
  const nonZeroCons = flip(addId("x"));
  const constrainedUniv = forall("x", "R", inv("x"), nonZeroCons);

  e.observePositive("R", addId("0"), "w_add0");
  e.observeNegative("R", addId("2"), "w_nadd2");
  e.observePositive("R", inv("2"), "w_inv2");
  e.observeNegative("R", inv("0"), "w_ninv0");
  e.closeDomain("R");

  // 1. Bug A: forall-elim on R ⊩+ ∀(x : R ⊓ [~AddId(x)]) Invertible(x) MUST enforce domainConstraint!
  const missingConstraintProof = verifyDerivation(e, {
    kind: "forall-elim",
    universal: { kind: "live-ground", boundary: "R", polarity: "+", item: constrainedUniv },
    term: "0",
  });
  assert.equal(missingConstraintProof.ok, false);
  if (!missingConstraintProof.ok) {
    assert.equal(missingConstraintProof.violation, "type-mismatch");
  }

  const failedConstraintProof = verifyDerivation(e, {
    kind: "forall-elim",
    universal: { kind: "live-ground", boundary: "R", polarity: "+", item: constrainedUniv },
    term: "0",
    constraintProof: {
      kind: "live-ground",
      boundary: "R",
      polarity: "+",
      item: flip(addId("0")),
    },
  });
  assert.equal(failedConstraintProof.ok, false);
  if (!failedConstraintProof.ok) {
    assert.equal(failedConstraintProof.violation, "ground-not-live");
  }

  const validConstrainedElim = verifyDerivation(e, {
    kind: "forall-elim",
    universal: { kind: "live-ground", boundary: "R", polarity: "+", item: constrainedUniv },
    term: "2",
    constraintProof: {
      kind: "live-ground",
      boundary: "R",
      polarity: "+",
      item: flip(addId("2")),
    },
  });
  assert.equal(validConstrainedElim.ok, true);
  if (validConstrainedElim.ok) {
    assert.equal(itemKey(validConstrainedElim.item), itemKey(inv("2")));
    assert.equal(validConstrainedElim.requiredBaseIds.includes("w_nadd2"), true);
  }

  // Reject spurious constraintProof when universal has NO domainConstraint
  const unconstrainedUniv = forall("x", "R", equiv("R", "x", "x"));
  const snapExtra = e.evaluate([unconstrainedUniv]);
  assert.equal(snapExtra.isLive("R", "+", unconstrainedUniv), true);
  const strayConstraintProof = verifyDerivation(e, {
    kind: "forall-elim",
    universal: { kind: "live-ground", boundary: "R", polarity: "+", item: unconstrainedUniv },
    term: "2",
    constraintProof: { kind: "equiv-refl", boundary: "R", term: "2" },
  });
  assert.equal(strayConstraintProof.ok, false);
  if (!strayConstraintProof.ok) {
    assert.equal(strayConstraintProof.violation, "type-mismatch");
  }

  // 2. Constrained forall-intro: valid discharge, shadowed-assumption, domainConstraint freshness, and missing pairing
  const validForallIntroCons = verifyDerivation(e, {
    kind: "forall-intro",
    boundary: "R",
    variable: "x",
    domain: "R",
    eigenvar: "α",
    templateBody: flip(addId("x")),
    domainConstraint: nonZeroCons,
    constraintAssumpId: "hNonZero",
    body: { kind: "assume", assumptionId: "hNonZero", boundary: "R" },
  });
  assert.equal(validForallIntroCons.ok, true);
  if (validForallIntroCons.ok) {
    assert.equal(itemKey(validForallIntroCons.item), itemKey(forall("x", "R", flip(addId("x")), nonZeroCons)));
  }

  const shadowedConstraintAssump = verifyDerivation(e, {
    kind: "implies-intro",
    boundary: "R",
    assumptionId: "hDup",
    antecedent: inv("2"),
    body: {
      kind: "forall-intro",
      boundary: "R",
      variable: "x",
      domain: "R",
      eigenvar: "α",
      templateBody: flip(addId("x")),
      domainConstraint: nonZeroCons,
      constraintAssumpId: "hDup",
      body: { kind: "assume", assumptionId: "hDup", boundary: "R" },
    },
  });
  assert.equal(shadowedConstraintAssump.ok, false);
  if (!shadowedConstraintAssump.ok) {
    assert.equal(shadowedConstraintAssump.violation, "shadowed-assumption");
  }

  const freshCollisionInConstraint = verifyDerivation(e, {
    kind: "forall-intro",
    boundary: "R",
    variable: "x",
    domain: "R",
    eigenvar: "0",
    templateBody: inv("x"),
    domainConstraint: flip(addId("0")),
    constraintAssumpId: "hZero",
    body: { kind: "assume", assumptionId: "hZero", boundary: "R" },
  });
  assert.equal(freshCollisionInConstraint.ok, false);
  if (!freshCollisionInConstraint.ok) {
    assert.equal(freshCollisionInConstraint.violation, "eigenvariable-not-fresh");
  }

  // Also test bound-variable collision inside domainConstraint: eigenvar "u" equals inner bound "u"
  const boundCollisionInConstraint = verifyDerivation(e, {
    kind: "forall-intro",
    boundary: "R",
    variable: "x",
    domain: "R",
    eigenvar: "u",
    templateBody: inv("x"),
    domainConstraint: exists("u", "R", flip(addId("u"))),
    constraintAssumpId: "hBound",
    body: {
      kind: "forall-elim",
      universal: { kind: "live-ground", boundary: "R", polarity: "+", item: constrainedUniv },
      term: "u",
    },
  });
  assert.equal(boundCollisionInConstraint.ok, false);
  if (!boundCollisionInConstraint.ok) {
    assert.equal(boundCollisionInConstraint.violation, "eigenvariable-not-fresh");
  }

  // 3. Constrained exists-intro & exists-elim
  const validExIntroCons = verifyDerivation(e, {
    kind: "exists-intro",
    witnessTerm: "2",
    variable: "x",
    domain: "R",
    templateBody: inv("x"),
    domainConstraint: nonZeroCons,
    constraintProof: {
      kind: "live-ground",
      boundary: "R",
      polarity: "+",
      item: flip(addId("2")),
    },
    witnessProof: { kind: "live-ground", boundary: "R", polarity: "+", item: inv("2") },
  });
  assert.equal(validExIntroCons.ok, true);
  if (validExIntroCons.ok) {
    assert.equal(itemKey(validExIntroCons.item), itemKey(exists("x", "R", inv("x"), nonZeroCons)));
  }

  const missingExConstraintProof = verifyDerivation(e, {
    kind: "exists-intro",
    witnessTerm: "2",
    variable: "x",
    domain: "R",
    templateBody: inv("x"),
    domainConstraint: nonZeroCons,
    witnessProof: { kind: "live-ground", boundary: "R", polarity: "+", item: inv("2") },
  });
  assert.equal(missingExConstraintProof.ok, false);
  if (!missingExConstraintProof.ok) {
    assert.equal(missingExConstraintProof.violation, "type-mismatch");
  }

  // exists-elim passes +δ(γ) into body to feed constrained forall-elim without γ escaping conclusion!
  const constrainedExItem = exists("x", "R", inv("x"), nonZeroCons);
  const safeRes = atom("SafeResult");
  const safeConsAll = forall("x", "R", implies(flip(addId("x")), safeRes), nonZeroCons);
  const validExElimCons = verifyDerivation(e, {
    kind: "implies-intro",
    boundary: "R",
    assumptionId: "hSafeAll",
    antecedent: safeConsAll,
    body: {
      kind: "implies-intro",
      boundary: "R",
      assumptionId: "hExCons",
      antecedent: constrainedExItem,
      body: {
        kind: "exists-elim",
        existential: { kind: "assume", assumptionId: "hExCons", boundary: "R" },
        witnessVar: "γ",
        assumptionId: "hBodyInv",
        constraintAssumpId: "hBodyNonZero",
        body: {
          kind: "implies-elim",
          premise: { kind: "assume", assumptionId: "hBodyNonZero", boundary: "R" },
          conditional: {
            kind: "forall-elim",
            universal: { kind: "assume", assumptionId: "hSafeAll", boundary: "R" },
            term: "γ",
            constraintProof: { kind: "assume", assumptionId: "hBodyNonZero", boundary: "R" },
          },
        },
      },
    },
  });
  assert.equal(validExElimCons.ok, true);

  const shadowedExElimIds = verifyDerivation(e, {
    kind: "implies-intro",
    boundary: "R",
    assumptionId: "hExCons",
    antecedent: constrainedExItem,
    body: {
      kind: "exists-elim",
      existential: { kind: "assume", assumptionId: "hExCons", boundary: "R" },
      witnessVar: "γ",
      assumptionId: "hSame",
      constraintAssumpId: "hSame",
      body: { kind: "assume", assumptionId: "hSame", boundary: "R" },
    },
  });
  assert.equal(shadowedExElimIds.ok, false);
  if (!shadowedExElimIds.ok) {
    assert.equal(shadowedExElimIds.violation, "shadowed-assumption");
  }
}

test(
  "deduction quantifier domainConstraint enforcement",
  test_deduction_quantifier_domain_constraint_enforcement,
);
test("eigenvariable freshness and one-position congruence", test_eigenvariable_freshness_and_one_position_congruence);
