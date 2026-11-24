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
  exists,
  forall,
  implies,
  itemKey,
  ref,
  structImposs,
} from "../src/syntax.ts";

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
  assert.equal(snap0.statusOf("Z", p), "Grounded");
  assert.equal(snap0.isLive("Z", "+", p), true);
  assert.equal(snap0.statusOf("Z", q), "Excluded");
  assert.equal(snap0.isLive("Z", "-", q), true);
  assert.equal(snap0.statusOf("Z", r), "Open");

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
  assert.equal(snapAdmitColl.statusOf("Odd", p), "Collision");
  assert.equal(snapAdmitColl.isObstructed("Z", p), true);
  assert.equal(snapAdmitColl.isLive("Z", "+", p), false);

  // Without an explicit entry on Z, colliding one cover cell suppresses Rule I gluing cleanly (no ghost Z ⊩+ P)
  engine.observeNegative("Odd", p, "w_odd_refute");
  const snapColl = engine.evaluate([p]);
  assert.equal(snapColl.statusOf("Odd", p), "Collision");
  assert.equal(snapColl.statusOf("Z", p), "Open");
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
  assert.equal(snapColl.statusOf("B", c), "Collision");
  assert.equal(snapColl.isLive("B", "+", implies(a, c)), false);

  // Retracting w_c cleanly withdraws the admitted theorem back to Open (zero ghost theorem)
  assert.equal(engine.retract("w_c"), true);
  const snapRetract = engine.evaluate([implies(a, c)]);
  assert.equal(snapRetract.statusOf("B", implies(a, c)), "Open");
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

test("standalone Cover-Gluing and Quarantine propagation", test_standalone_cover_gluing_and_quarantine_propagation);
test("natural deduction implies-intro, anti-vacuity, and Quarantine bridge", test_natural_deduction_implies_intro_and_anti_vacuity_quarantine);
test("schematic forall-intro and exists-elim eigenvariable soundness on open domains", test_schematic_forall_intro_eigenvariable_soundness_on_open_domains);
test("UL-Minimal vs UL-Intuitionistic proof-theoretic separation", test_ul_minimal_vs_ul_intuitionistic_proof_theoretic_separation);
