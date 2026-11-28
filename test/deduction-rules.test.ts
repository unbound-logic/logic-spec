import assert from "node:assert/strict";
import { test } from "node:test";
import { BOT_BOUNDARY, BoundarySystem } from "../src/boundary.ts";
import {
  admitVerifiedDerivation,
  verifyDerivation,
  type DeductionMode,
  type DerivationResult,
  type ProofNode,
  type ProofViolation,
} from "../src/deduction.ts";
import { InquiryEngine, type CoverDependency, type EngineOptions, type GroundDependency } from "../src/engine.ts";
import {
  and,
  atom,
  bottom,
  equiv,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  refl,
  reflStatus,
  type Item,
  type Polarity,
} from "../src/syntax.ts";

// One table row per proof rule of verifyDerivation (src/deduction.ts). Each row holds proofs the
// checker must accept, with the judgment and dependencies they derive, and near misses it must
// reject, one per rejection condition of the rule, each with the violation it must report. A near
// miss breaks exactly one condition, so a checker that drops that condition accepts it or reports
// another violation. The table is keyed by ProofNode["kind"]: a new rule without a row fails the
// typecheck.

// ---------------------------------------------------------------------------------------------
// Fixture
// ---------------------------------------------------------------------------------------------

const A = atom("A");
const C = atom("C");
const E = atom("E");
const N = atom("N");
const P = atom("P");
const Q = atom("Q");
const S = atom("S");
const r = (h: string): Item => atom("R", [{ role: "arg", handle: h }]);
const pos = (h: string): Item => atom("Pos", [{ role: "arg", handle: h }]);
const rel = (from: string, to: string): Item => atom("Rel", [{ role: "from", handle: from }, { role: "to", handle: to }]);
const alien = (from: string, to: string): Item => atom("Alien", [{ role: "from", handle: from }, { role: "to", handle: to }]);

/**
 * The boundary system every case starts from:
 * - B holds the handles h1, h2, zz and the native relations R, Pos and Rel; H ⊑ B is a quantifier
 *   domain without zz.
 * - L and M lie below B and meet in LM; D1 and D2 lie below B and are declared disjoint; U1 and U2
 *   are unrelated, so their overlap is unknown. L and H share no sub-boundary, so theirs is unknown.
 * - K is covered by its disjoint cells K1 and K2, and K1 by its disjoint cells K11 and K12.
 */
function world(options: EngineOptions = {}): InquiryEngine {
  const b = new BoundarySystem();
  const handles = (ids: readonly string[]) => ids.map((id) => ({ id, criterion: `I(${id})`, kind: "structural" as const }));
  b.defineBoundary("B", { nativeRelations: ["R", "Pos", "Rel"], handles: handles(["h1", "h2", "zz"]) });
  b.defineBoundary("H", { parents: ["B"], handles: handles(["h1", "h2"]) });
  b.defineBoundary("L", { parents: ["B"] });
  b.defineBoundary("M", { parents: ["B"] });
  b.defineBoundary("LM", { parents: ["L", "M"] });
  b.defineMeet("L", "M", "LM");
  b.defineBoundary("D1", { parents: ["B"] });
  b.defineBoundary("D2", { parents: ["B"] });
  b.declareDisjoint("D1", "D2");
  b.defineBoundary("U1");
  b.defineBoundary("U2");
  b.defineBoundary("K");
  b.defineBoundary("K1", { parents: ["K"] });
  b.defineBoundary("K2", { parents: ["K"] });
  b.declareDisjoint("K1", "K2");
  b.defineBoundary("K11", { parents: ["K1"] });
  b.defineBoundary("K12", { parents: ["K1"] });
  b.declareDisjoint("K11", "K12");
  const e = new InquiryEngine(b, options);
  e.witnessCover("K", ["K1", "K2"]);
  e.witnessCover("K1", ["K11", "K12"]);
  return e;
}

/** A base observation: polarity, boundary, item, base identifier. */
type Obs = readonly [Polarity, string, Item, string];

let obsCounter = 0;

/** The fixture world with `observations` recorded in order. */
function given(observations: readonly Obs[], options: EngineOptions = {}): InquiryEngine {
  const e = world(options);
  for (const [polarity, boundary, item, baseId] of observations) {
    if (polarity === "+") {
      e.observePositive(boundary, item, baseId);
    } else {
      e.observeNegative(boundary, item, baseId);
    }
  }
  return e;
}

/** A base observation whose identifier the case does not name. */
function o(polarity: Polarity, boundary: string, item: Item): Obs {
  obsCounter += 1;
  return [polarity, boundary, item, `w${obsCounter}`];
}

/** A Live-ground leaf; `baseId` names a base observation of it. */
function live(boundary: string, item: Item, opts: { readonly polarity?: Polarity; readonly baseId?: string } = {}): ProofNode {
  const polarity = opts.polarity ?? "+";
  return opts.baseId === undefined
    ? { kind: "live-ground", boundary, polarity, item }
    : { kind: "live-ground", boundary, polarity, item, baseId: opts.baseId };
}

function hyp(assumptionId: string, boundary = "B"): ProofNode {
  return { kind: "assume", assumptionId, boundary };
}

/**
 * (boundary, +, item) through flip-elim from the record (boundary, -, ~item), which evaluation
 * derives from a Live (boundary, +, item). ~item is in Σ only when the checker evaluates it, so the
 * leaf is found only when the checker collects it.
 */
function viaFlip(boundary: string, item: Item): ProofNode {
  return { kind: "flip-elim", inner: live(boundary, flip(item), { polarity: "-" }) };
}

function intro(boundary: string, assumptionId: string, antecedent: Item, body: ProofNode): ProofNode {
  return { kind: "implies-intro", boundary, assumptionId, antecedent, body };
}

function elim(premise: ProofNode, conditional: ProofNode): ProofNode {
  return { kind: "implies-elim", premise, conditional };
}

function g(boundary: string, item: Item, polarity: Polarity = "+"): GroundDependency {
  return { boundary, polarity, item };
}

// ---------------------------------------------------------------------------------------------
// Table types and harness
// ---------------------------------------------------------------------------------------------

type Built = { readonly engine: InquiryEngine; readonly proof: ProofNode; readonly mode?: DeductionMode };

type Expected = {
  readonly boundary: string;
  readonly polarity: Polarity;
  readonly item: Item;
  readonly requiredBaseIds: readonly string[];
  readonly requiredGrounds: readonly GroundDependency[];
  /** Defaults to none. */
  readonly requiredCovers?: readonly CoverDependency[];
};

type AcceptCase = { readonly name: string; readonly build: () => Built; readonly expect: Expected };
type RejectCase = { readonly name: string; readonly build: () => Built; readonly violation: ProofViolation };
type RuleCases = {
  readonly accept: readonly [AcceptCase, ...AcceptCase[]];
  readonly reject: readonly [RejectCase, ...RejectCase[]];
};

function built(engine: InquiryEngine, proof: ProofNode, mode?: DeductionMode): Built {
  return mode === undefined ? { engine, proof } : { engine, proof, mode };
}

const groundKey = (d: GroundDependency): string => `${d.boundary} ${d.polarity} ${itemKey(d.item)}`;

/** The kinds of every proof node of `proof`. */
function kindsIn(proof: ProofNode, kinds: ReadonlySet<string>): Set<string> {
  const out = new Set<string>();
  const visit = (node: ProofNode): void => {
    out.add(node.kind);
    for (const value of Object.values(node)) {
      if (Array.isArray(value)) {
        for (const el of value) {
          visit((el as { readonly proof: ProofNode }).proof);
        }
      } else if (value !== null && typeof value === "object" && kinds.has((value as { readonly kind: string }).kind)) {
        visit(value as ProofNode);
      }
    }
  };
  visit(proof);
  return out;
}

function checkAccept(kind: string, c: AcceptCase, kinds: ReadonlySet<string>): void {
  const { engine, proof, mode } = c.build();
  assert.ok(kindsIn(proof, kinds).has(kind), `the proof uses ${kind}`);
  const res: DerivationResult = verifyDerivation(engine, proof, mode);
  assert.equal(res.ok ? "accepted" : `${res.violation}: ${res.reason}`, "accepted");
  if (!res.ok) {
    return;
  }
  assert.equal(res.boundary, c.expect.boundary, "boundary");
  assert.equal(res.polarity, c.expect.polarity, "polarity");
  assert.equal(itemKey(res.item), itemKey(c.expect.item), "item");
  assert.deepEqual(res.requiredBaseIds, c.expect.requiredBaseIds, "requiredBaseIds");
  assert.deepEqual(res.requiredGrounds.map(groundKey), c.expect.requiredGrounds.map(groundKey), "requiredGrounds");
  assert.deepEqual(res.requiredCovers, c.expect.requiredCovers ?? [], "requiredCovers");
}

function checkReject(kind: string, c: RejectCase, kinds: ReadonlySet<string>): void {
  const { engine, proof, mode } = c.build();
  assert.ok(kindsIn(proof, kinds).has(kind), `the proof uses ${kind}`);
  const res = verifyDerivation(engine, proof, mode);
  assert.equal(res.ok ? "accepted" : res.violation, c.violation);
  if (!res.ok) {
    // The violation is the contract; the reason is free text, but a rejection always explains itself.
    assert.ok(res.reason.length > 0, "a rejection gives a reason");
  }
}

// ---------------------------------------------------------------------------------------------
// The rule table
// ---------------------------------------------------------------------------------------------

const U = forall("x", "H", r("x"));
const UC = forall("x", "H", r("x"), pos("x"));
const X = exists("x", "H", r("x"));
const XC = exists("x", "H", r("x"), pos("x"));
const EQ = equiv("B", "h1", "h2");
const NB = implies(A, bottom());

function orElim(disjunction: ProofNode, leftBranch: ProofNode, rightBranch: ProofNode): ProofNode {
  return { kind: "or-elim", disjunction, leftAssumpId: "hl", leftBranch, rightAssumpId: "hr", rightBranch };
}

/** An engine at stage t where +P and +Q are Live on B, followed by one more stage. */
function staged(): { readonly engine: InquiryEngine; readonly t: number } {
  const engine = given([["+", "B", P, "p"], ["+", "B", Q, "q"]]);
  const t = engine.stage;
  engine.observePositive("B", S, "later");
  return { engine, t };
}

/** An engine at stage t where +P on B is Undetermined (an incompatibility with a Live +Q). */
function stagedUndetermined(): { readonly engine: InquiryEngine; readonly t: number } {
  const engine = given([["+", "B", P, "p"], ["+", "B", Q, "q"]]);
  engine.addIncompatibility("B", P, Q);
  const t = engine.stage;
  engine.observePositive("B", S, "later");
  return { engine, t };
}

/** The reflected stages of staged() and stagedUndetermined(); both builders are deterministic. */
const T = staged().t;
const TU = stagedUndetermined().t;

function exFalsoProof(bottomProof: ProofNode): ProofNode {
  return intro("B", "h", A, { kind: "ex-falso-bottom", bottomProof, target: C });
}

const ALL_TO_P = forall("y", "H", implies(r("y"), P));
const ALL_POS_TO_P = forall("y", "H", implies(pos("y"), P));

const RULE_CASES: { readonly [K in ProofNode["kind"]]: RuleCases } = {
  "live-ground": {
    accept: [
      {
        name: "a Live ground without a named base observation",
        build: () => built(given([["+", "B", P, "p"]]), live("B", P)),
        expect: { boundary: "B", polarity: "+", item: P, requiredBaseIds: [], requiredGrounds: [g("B", P)] },
      },
      {
        name: "a Live ground naming one of its base observations",
        build: () => built(given([["+", "B", P, "p1"], ["+", "B", P, "p2"]]), live("B", P, { baseId: "p2" })),
        expect: { boundary: "B", polarity: "+", item: P, requiredBaseIds: ["p2"], requiredGrounds: [g("B", P)] },
      },
      {
        name: "a negative Live ground",
        build: () => built(given([["-", "B", N, "n"]]), live("B", N, { polarity: "-" })),
        expect: { boundary: "B", polarity: "-", item: N, requiredBaseIds: [], requiredGrounds: [g("B", N, "-")] },
      },
    ],
    reject: [
      { name: "an undefined boundary", build: () => built(given([["+", "B", P, "p"]]), live("Nowhere", P)), violation: "invalid-boundary" },
      { name: "the empty boundary", build: () => built(given([["+", "B", P, "p"]]), live(BOT_BOUNDARY, P)), violation: "invalid-boundary" },
      { name: "a ground nothing records", build: () => built(given([["+", "B", Q, "q"]]), live("B", P)), violation: "ground-not-live" },
      {
        name: "a named base observation of another item",
        build: () => built(given([["+", "B", P, "p"], ["+", "B", Q, "q"]]), live("B", P, { baseId: "q" })),
        violation: "ground-not-live",
      },
      {
        name: "a named base observation that does not exist",
        build: () => built(given([["+", "B", P, "p"]]), live("B", P, { baseId: "nope" })),
        violation: "ground-not-live",
      },
    ],
  },

  assume: {
    accept: [
      {
        name: "an assumption at its own boundary",
        build: () => built(given([]), intro("B", "h", A, hyp("h"))),
        expect: { boundary: "B", polarity: "+", item: implies(A, A), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "an assumption at boundaries that refine its scope",
        build: () =>
          built(
            given([]),
            intro("K", "h", A, {
              kind: "cover-glue",
              boundary: "K",
              item: A,
              cellProofs: [
                { cell: "K1", proof: hyp("h", "K1") },
                { cell: "K2", proof: hyp("h", "K2") },
              ],
            }),
          ),
        expect: {
          boundary: "K",
          polarity: "+",
          item: implies(A, A),
          requiredBaseIds: [],
          requiredGrounds: [],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
    ],
    reject: [
      { name: "an assumption outside any discharge", build: () => built(given([]), hyp("h")), violation: "unknown-assumption" },
      { name: "an assumption no discharge names", build: () => built(given([]), intro("B", "h", A, hyp("g"))), violation: "unknown-assumption" },
      { name: "an assumption at an undefined boundary", build: () => built(given([]), intro("B", "h", A, hyp("h", "Nowhere"))), violation: "invalid-boundary" },
      { name: "an assumption at the empty boundary", build: () => built(given([]), intro("B", "h", A, hyp("h", BOT_BOUNDARY))), violation: "invalid-boundary" },
      { name: "an assumption at a boundary coarser than its scope", build: () => built(given([]), intro("L", "h", A, hyp("h", "B"))), violation: "invalid-boundary" },
    ],
  },

  "weaken-boundary": {
    accept: [
      {
        name: "a positive ground weakened to a sub-boundary",
        build: () => built(given([["+", "B", P, "p"]]), { kind: "weaken-boundary", proof: live("B", P, { baseId: "p" }), toBoundary: "L" }),
        expect: { boundary: "L", polarity: "+", item: P, requiredBaseIds: ["p"], requiredGrounds: [g("B", P)] },
      },
      {
        name: "a negative ground weakened to a sub-boundary",
        build: () => built(given([["-", "B", N, "n"]]), { kind: "weaken-boundary", proof: live("B", N, { polarity: "-" }), toBoundary: "L" }),
        expect: { boundary: "L", polarity: "-", item: N, requiredBaseIds: [], requiredGrounds: [g("B", N, "-")] },
      },
      {
        name: "a derived premise",
        build: () => built(given([o("+", "B", P)]), { kind: "weaken-boundary", proof: viaFlip("B", P), toBoundary: "L" }),
        expect: { boundary: "L", polarity: "+", item: P, requiredBaseIds: [], requiredGrounds: [g("B", flip(P), "-")] },
      },
    ],
    reject: [
      {
        name: "an undefined target boundary",
        build: () => built(given([o("+", "B", P)]), { kind: "weaken-boundary", proof: live("B", P), toBoundary: "Nowhere" }),
        violation: "invalid-boundary",
      },
      {
        name: "the empty target boundary",
        build: () => built(given([o("+", "B", P)]), { kind: "weaken-boundary", proof: live("B", P), toBoundary: BOT_BOUNDARY }),
        violation: "invalid-boundary",
      },
      {
        name: "a premise that fails",
        build: () => built(given([]), { kind: "weaken-boundary", proof: live("B", P), toBoundary: "L" }),
        violation: "ground-not-live",
      },
      {
        name: "a target coarser than the premise",
        build: () => built(given([o("+", "L", P)]), { kind: "weaken-boundary", proof: live("L", P), toBoundary: "B" }),
        violation: "invalid-boundary",
      },
    ],
  },

  "implies-intro": {
    accept: [
      {
        name: "a discharge of an assumption the body uses",
        build: () => built(given([["+", "B", implies(A, C), "ac"]]), intro("B", "h", A, elim(hyp("h"), live("B", implies(A, C), { baseId: "ac" })))),
        expect: { boundary: "B", polarity: "+", item: implies(A, C), requiredBaseIds: ["ac"], requiredGrounds: [g("B", implies(A, C))] },
      },
      {
        name: "a vacuous discharge",
        build: () => built(given([["+", "B", P, "p"]]), intro("B", "h", A, live("B", P, { baseId: "p" }))),
        expect: { boundary: "B", polarity: "+", item: implies(A, P), requiredBaseIds: ["p"], requiredGrounds: [g("B", P)] },
      },
    ],
    reject: [
      { name: "an undefined boundary", build: () => built(given([o("+", "B", P)]), intro("Nowhere", "h", A, live("B", P))), violation: "invalid-boundary" },
      { name: "the empty boundary", build: () => built(given([o("+", "B", P)]), intro(BOT_BOUNDARY, "h", A, live("B", P))), violation: "invalid-boundary" },
      {
        name: "an assumption identifier that shadows an open one",
        build: () => built(given([]), intro("B", "h", A, intro("B", "h", C, hyp("h")))),
        violation: "shadowed-assumption",
      },
      { name: "a body that fails", build: () => built(given([]), intro("B", "h", A, live("B", P))), violation: "ground-not-live" },
      { name: "a negative body", build: () => built(given([o("-", "B", N)]), intro("B", "h", A, live("B", N, { polarity: "-" }))), violation: "type-mismatch" },
      { name: "a body at another boundary", build: () => built(given([o("+", "L", P)]), intro("B", "h", A, live("L", P))), violation: "type-mismatch" },
    ],
  },

  "implies-elim": {
    accept: [
      {
        name: "Scoped Cut at the meet of the premises' boundaries",
        build: () =>
          built(
            given([["+", "L", A, "z_a"], ["+", "M", implies(A, C), "a_ac"]]),
            elim(live("L", A, { baseId: "z_a" }), live("M", implies(A, C), { baseId: "a_ac" })),
          ),
        expect: {
          boundary: "LM",
          polarity: "+",
          item: C,
          requiredBaseIds: ["a_ac", "z_a"],
          requiredGrounds: [g("L", A), g("M", implies(A, C))],
        },
      },
      {
        name: "a derived premise and a derived conditional",
        build: () => built(given([o("+", "B", A), o("+", "B", implies(A, C))]), elim(viaFlip("B", A), viaFlip("B", implies(A, C)))),
        expect: {
          boundary: "B",
          polarity: "+",
          item: C,
          requiredBaseIds: [],
          requiredGrounds: [g("B", flip(A), "-"), g("B", flip(implies(A, C)), "-")],
        },
      },
    ],
    reject: [
      { name: "a premise that fails", build: () => built(given([o("+", "B", implies(A, C))]), elim(live("B", A), live("B", implies(A, C)))), violation: "ground-not-live" },
      { name: "a conditional that fails", build: () => built(given([o("+", "B", A)]), elim(live("B", A), live("B", implies(A, C)))), violation: "ground-not-live" },
      {
        name: "a negative premise",
        build: () => built(given([o("-", "B", A), o("+", "B", implies(A, C))]), elim(live("B", A, { polarity: "-" }), live("B", implies(A, C)))),
        violation: "type-mismatch",
      },
      {
        name: "a negative conditional",
        build: () => built(given([o("+", "B", A), o("-", "B", implies(A, C))]), elim(live("B", A), live("B", implies(A, C), { polarity: "-" }))),
        violation: "type-mismatch",
      },
      { name: "a conditional that is no conditional", build: () => built(given([o("+", "B", A), o("+", "B", C)]), elim(live("B", A), live("B", C))), violation: "type-mismatch" },
      {
        name: "a premise that is not the antecedent",
        build: () => built(given([o("+", "B", A), o("+", "B", implies(C, E))]), elim(live("B", A), live("B", implies(C, E)))),
        violation: "type-mismatch",
      },
      {
        name: "premises over an unknown overlap",
        build: () => built(given([o("+", "U1", A), o("+", "U2", implies(A, C))]), elim(live("U1", A), live("U2", implies(A, C)))),
        violation: "unknown-meet",
      },
      {
        name: "premises on disjoint boundaries",
        build: () => built(given([o("+", "D1", A), o("+", "D2", implies(A, C))]), elim(live("D1", A), live("D2", implies(A, C)))),
        violation: "disjoint-meet",
      },
    ],
  },

  "and-intro": {
    accept: [
      {
        name: "conjuncts at the meet of their boundaries",
        build: () =>
          built(given([["+", "L", A, "z_a"], ["+", "M", C, "a_c"]]), { kind: "and-intro", left: live("L", A, { baseId: "z_a" }), right: live("M", C, { baseId: "a_c" }) }),
        expect: { boundary: "LM", polarity: "+", item: and(A, C), requiredBaseIds: ["a_c", "z_a"], requiredGrounds: [g("L", A), g("M", C)] },
      },
      {
        name: "the same ground twice, one dependency",
        build: () => built(given([["+", "B", P, "p"]]), { kind: "and-intro", left: live("B", P, { baseId: "p" }), right: live("B", P, { baseId: "p" }) }),
        expect: { boundary: "B", polarity: "+", item: and(P, P), requiredBaseIds: ["p"], requiredGrounds: [g("B", P)] },
      },
      {
        name: "derived conjuncts",
        build: () => built(given([o("+", "B", A), o("+", "B", C)]), { kind: "and-intro", left: viaFlip("B", A), right: viaFlip("B", C) }),
        expect: { boundary: "B", polarity: "+", item: and(A, C), requiredBaseIds: [], requiredGrounds: [g("B", flip(A), "-"), g("B", flip(C), "-")] },
      },
      {
        name: "the same cover twice, one cover dependency",
        build: () => {
          const glue: ProofNode = {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", A) },
            ],
          };
          return built(given([["+", "K1", A, "a1"], ["+", "K2", A, "a2"]]), { kind: "and-intro", left: glue, right: glue });
        },
        expect: {
          boundary: "K",
          polarity: "+",
          item: and(A, A),
          requiredBaseIds: [],
          requiredGrounds: [g("K1", A), g("K2", A)],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
    ],
    reject: [
      { name: "a left conjunct that fails", build: () => built(given([o("+", "B", C)]), { kind: "and-intro", left: live("B", A), right: live("B", C) }), violation: "ground-not-live" },
      { name: "a right conjunct that fails", build: () => built(given([o("+", "B", A)]), { kind: "and-intro", left: live("B", A), right: live("B", C) }), violation: "ground-not-live" },
      {
        name: "a negative left conjunct",
        build: () => built(given([o("-", "B", A), o("+", "B", C)]), { kind: "and-intro", left: live("B", A, { polarity: "-" }), right: live("B", C) }),
        violation: "type-mismatch",
      },
      {
        name: "a negative right conjunct",
        build: () => built(given([o("+", "B", A), o("-", "B", C)]), { kind: "and-intro", left: live("B", A), right: live("B", C, { polarity: "-" }) }),
        violation: "type-mismatch",
      },
      {
        name: "conjuncts over an unknown overlap",
        build: () => built(given([o("+", "U1", A), o("+", "U2", C)]), { kind: "and-intro", left: live("U1", A), right: live("U2", C) }),
        violation: "unknown-meet",
      },
      {
        name: "conjuncts on disjoint boundaries",
        build: () => built(given([o("+", "D1", A), o("+", "D2", C)]), { kind: "and-intro", left: live("D1", A), right: live("D2", C) }),
        violation: "disjoint-meet",
      },
    ],
  },

  "and-elim": {
    accept: [
      {
        name: "the left conjunct",
        build: () => built(given([["+", "B", and(A, C), "ac"]]), { kind: "and-elim", pair: live("B", and(A, C), { baseId: "ac" }), side: "left" }),
        expect: { boundary: "B", polarity: "+", item: A, requiredBaseIds: ["ac"], requiredGrounds: [g("B", and(A, C))] },
      },
      {
        name: "the right conjunct",
        build: () => built(given([["+", "B", and(A, C), "ac"]]), { kind: "and-elim", pair: live("B", and(A, C), { baseId: "ac" }), side: "right" }),
        expect: { boundary: "B", polarity: "+", item: C, requiredBaseIds: ["ac"], requiredGrounds: [g("B", and(A, C))] },
      },
      {
        name: "a conjunction only evaluation derives",
        build: () => built(given([o("+", "B", A), o("+", "B", C)]), { kind: "and-elim", pair: live("B", and(A, C)), side: "left" }),
        expect: { boundary: "B", polarity: "+", item: A, requiredBaseIds: [], requiredGrounds: [g("B", and(A, C))] },
      },
    ],
    reject: [
      { name: "a conjunction that fails", build: () => built(given([]), { kind: "and-elim", pair: live("B", and(A, C)), side: "left" }), violation: "ground-not-live" },
      {
        name: "a negative conjunction",
        build: () => built(given([o("-", "B", and(A, C))]), { kind: "and-elim", pair: live("B", and(A, C), { polarity: "-" }), side: "left" }),
        violation: "type-mismatch",
      },
      { name: "a premise that is no conjunction", build: () => built(given([o("+", "B", A)]), { kind: "and-elim", pair: live("B", A), side: "left" }), violation: "type-mismatch" },
    ],
  },

  "or-intro": {
    accept: [
      {
        name: "a left disjunct",
        build: () => built(given([["+", "B", A, "a"]]), { kind: "or-intro", witness: live("B", A, { baseId: "a" }), side: "left", other: C }),
        expect: { boundary: "B", polarity: "+", item: or(A, C), requiredBaseIds: ["a"], requiredGrounds: [g("B", A)] },
      },
      {
        name: "a right disjunct",
        build: () => built(given([["+", "B", A, "a"]]), { kind: "or-intro", witness: live("B", A, { baseId: "a" }), side: "right", other: C }),
        expect: { boundary: "B", polarity: "+", item: or(C, A), requiredBaseIds: ["a"], requiredGrounds: [g("B", A)] },
      },
      {
        name: "a derived witness",
        build: () => built(given([o("+", "B", A)]), { kind: "or-intro", witness: viaFlip("B", A), side: "left", other: C }),
        expect: { boundary: "B", polarity: "+", item: or(A, C), requiredBaseIds: [], requiredGrounds: [g("B", flip(A), "-")] },
      },
    ],
    reject: [
      { name: "a witness that fails", build: () => built(given([]), { kind: "or-intro", witness: live("B", A), side: "left", other: C }), violation: "ground-not-live" },
      {
        name: "a negative witness",
        build: () => built(given([o("-", "B", A)]), { kind: "or-intro", witness: live("B", A, { polarity: "-" }), side: "left", other: C }),
        violation: "type-mismatch",
      },
    ],
  },

  "or-cover-intro": {
    accept: [
      {
        name: "each cell witnessing one disjunct",
        build: () =>
          built(given([["+", "K1", A, "z1"], ["+", "K2", C, "a2"]]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A, { baseId: "z1" }) },
              { cell: "K2", proof: live("K2", C, { baseId: "a2" }) },
            ],
          }),
        expect: {
          boundary: "K",
          polarity: "+",
          item: or(A, C),
          requiredBaseIds: ["a2", "z1"],
          requiredGrounds: [g("K1", A), g("K2", C)],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
      {
        name: "every cell witnessing the left disjunct, cells out of order",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", A)]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K2", proof: live("K2", A) },
              { cell: "K1", proof: live("K1", A) },
            ],
          }),
        expect: {
          boundary: "K",
          polarity: "+",
          item: or(A, C),
          requiredBaseIds: [],
          requiredGrounds: [g("K2", A), g("K1", A)],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
      {
        name: "derived cell witnesses",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", C)]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: viaFlip("K1", A) },
              { cell: "K2", proof: viaFlip("K2", C) },
            ],
          }),
        expect: {
          boundary: "K",
          polarity: "+",
          item: or(A, C),
          requiredBaseIds: [],
          requiredGrounds: [g("K1", flip(A), "-"), g("K2", flip(C), "-")],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
    ],
    reject: [
      {
        name: "an undefined boundary",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", C)]), {
            kind: "or-cover-intro",
            boundary: "Nowhere",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", C) },
            ],
          }),
        violation: "invalid-boundary",
      },
      {
        name: "the empty boundary",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", C)]), {
            kind: "or-cover-intro",
            boundary: BOT_BOUNDARY,
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", C) },
            ],
          }),
        violation: "invalid-boundary",
      },
      {
        name: "no cells",
        build: () => built(given([]), { kind: "or-cover-intro", boundary: "K", left: A, right: C, cellProofs: [] }),
        violation: "unwitnessed-cover",
      },
      {
        name: "cells that are no witnessed cover",
        build: () =>
          built(given([o("+", "K1", A)]), { kind: "or-cover-intro", boundary: "K", left: A, right: C, cellProofs: [{ cell: "K1", proof: live("K1", A) }] }),
        violation: "unwitnessed-cover",
      },
      {
        name: "a cell proof that fails",
        build: () =>
          built(given([o("+", "K1", A)]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", C) },
            ],
          }),
        violation: "ground-not-live",
      },
      {
        name: "a negative cell witness",
        build: () =>
          built(given([o("+", "K1", A), o("-", "K2", C)]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", C, { polarity: "-" }) },
            ],
          }),
        violation: "type-mismatch",
      },
      {
        name: "a cell witness at another boundary",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K", C)]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K", C) },
            ],
          }),
        violation: "type-mismatch",
      },
      {
        name: "a cell witness of neither disjunct",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", S)]), {
            kind: "or-cover-intro",
            boundary: "K",
            left: A,
            right: C,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", S) },
            ],
          }),
        violation: "type-mismatch",
      },
    ],
  },

  "or-elim": {
    accept: [
      {
        name: "both branches deriving the same item",
        build: () =>
          built(
            given([["+", "B", or(A, C), "z_or"], ["+", "B", implies(A, E), "m_ae"], ["+", "B", implies(C, E), "a_ce"]]),
            orElim(
              live("B", or(A, C), { baseId: "z_or" }),
              elim(hyp("hl"), live("B", implies(A, E), { baseId: "m_ae" })),
              elim(hyp("hr"), live("B", implies(C, E), { baseId: "a_ce" })),
            ),
          ),
        expect: {
          boundary: "B",
          polarity: "+",
          item: E,
          requiredBaseIds: ["a_ce", "m_ae", "z_or"],
          requiredGrounds: [g("B", or(A, C)), g("B", implies(A, E)), g("B", implies(C, E))],
        },
      },
      {
        name: "a derived disjunction and derived branch premises",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            orElim(viaFlip("B", or(A, C)), elim(hyp("hl"), viaFlip("B", implies(A, E))), elim(hyp("hr"), viaFlip("B", implies(C, E)))),
          ),
        expect: {
          boundary: "B",
          polarity: "+",
          item: E,
          requiredBaseIds: [],
          requiredGrounds: [g("B", flip(or(A, C)), "-"), g("B", flip(implies(A, E)), "-"), g("B", flip(implies(C, E)), "-")],
        },
      },
    ],
    reject: [
      {
        name: "a disjunction that fails",
        build: () =>
          built(
            given([o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, E)))),
          ),
        violation: "ground-not-live",
      },
      {
        name: "a negative disjunction",
        build: () =>
          built(
            given([o("-", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            orElim(live("B", or(A, C), { polarity: "-" }), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, E)))),
          ),
        violation: "type-mismatch",
      },
      {
        name: "a premise that is no disjunction",
        build: () =>
          built(
            given([o("+", "B", A), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            orElim(live("B", A), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, E)))),
          ),
        violation: "type-mismatch",
      },
      {
        name: "a left assumption identifier that shadows an open one",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            intro("B", "hl", S, orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, E))))),
          ),
        violation: "shadowed-assumption",
      },
      {
        name: "a right assumption identifier that shadows an open one",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            intro("B", "hr", S, orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, E))))),
          ),
        violation: "shadowed-assumption",
      },
      {
        name: "a left branch that fails",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(C, E))]),
            orElim(live("B", or(A, C)), hyp("nope"), elim(hyp("hr"), live("B", implies(C, E)))),
          ),
        violation: "unknown-assumption",
      },
      {
        name: "a right branch that fails",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E))]),
            orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), hyp("nope")),
          ),
        violation: "unknown-assumption",
      },
      {
        name: "a negative left branch",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("-", "B", E), o("+", "B", implies(C, E))]),
            orElim(live("B", or(A, C)), live("B", E, { polarity: "-" }), elim(hyp("hr"), live("B", implies(C, E)))),
          ),
        violation: "type-mismatch",
      },
      {
        name: "a negative right branch",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("-", "B", E)]),
            orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), live("B", E, { polarity: "-" })),
          ),
        violation: "type-mismatch",
      },
      {
        name: "a left branch at a sub-boundary",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            orElim(live("B", or(A, C)), elim(hyp("hl", "L"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, E)))),
          ),
        violation: "type-mismatch",
      },
      {
        name: "a right branch at a sub-boundary",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, E))]),
            orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr", "L"), live("B", implies(C, E)))),
          ),
        violation: "type-mismatch",
      },
      {
        name: "branches deriving different items",
        build: () =>
          built(
            given([o("+", "B", or(A, C)), o("+", "B", implies(A, E)), o("+", "B", implies(C, S))]),
            orElim(live("B", or(A, C)), elim(hyp("hl"), live("B", implies(A, E))), elim(hyp("hr"), live("B", implies(C, S)))),
          ),
        violation: "type-mismatch",
      },
    ],
  },

  "cover-glue": {
    accept: [
      {
        name: "positive cells",
        build: () =>
          built(given([["+", "K1", A, "z1"], ["+", "K2", A, "a2"]]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A, { baseId: "z1" }) },
              { cell: "K2", proof: live("K2", A, { baseId: "a2" }) },
            ],
          }),
        expect: {
          boundary: "K",
          polarity: "+",
          item: A,
          requiredBaseIds: ["a2", "z1"],
          requiredGrounds: [g("K1", A), g("K2", A)],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
      {
        name: "negative cells",
        build: () =>
          built(given([o("-", "K1", A), o("-", "K2", A)]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A, { polarity: "-" }) },
              { cell: "K2", proof: live("K2", A, { polarity: "-" }) },
            ],
          }),
        expect: {
          boundary: "K",
          polarity: "-",
          item: A,
          requiredBaseIds: [],
          requiredGrounds: [g("K1", A, "-"), g("K2", A, "-")],
          requiredCovers: [{ boundary: "K", cells: ["K1", "K2"] }],
        },
      },
      {
        name: "a cover glued inside a cell of another cover",
        build: () =>
          built(given([o("+", "K11", A), o("+", "K12", A), o("+", "K2", A)]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              {
                cell: "K1",
                proof: {
                  kind: "cover-glue",
                  boundary: "K1",
                  item: A,
                  cellProofs: [
                    { cell: "K12", proof: live("K12", A) },
                    { cell: "K11", proof: live("K11", A) },
                  ],
                },
              },
              { cell: "K2", proof: viaFlip("K2", A) },
            ],
          }),
        expect: {
          boundary: "K",
          polarity: "+",
          item: A,
          requiredBaseIds: [],
          requiredGrounds: [g("K12", A), g("K11", A), g("K2", flip(A), "-")],
          requiredCovers: [
            { boundary: "K", cells: ["K1", "K2"] },
            { boundary: "K1", cells: ["K11", "K12"] },
          ],
        },
      },
    ],
    reject: [
      {
        name: "an undefined boundary",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", A)]), {
            kind: "cover-glue",
            boundary: "Nowhere",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", A) },
            ],
          }),
        violation: "invalid-boundary",
      },
      {
        name: "the empty boundary",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", A)]), {
            kind: "cover-glue",
            boundary: BOT_BOUNDARY,
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", A) },
            ],
          }),
        violation: "invalid-boundary",
      },
      { name: "no cells", build: () => built(given([]), { kind: "cover-glue", boundary: "K", item: A, cellProofs: [] }), violation: "unwitnessed-cover" },
      {
        name: "cells that are no witnessed cover",
        build: () => built(given([o("+", "K1", A)]), { kind: "cover-glue", boundary: "K", item: A, cellProofs: [{ cell: "K1", proof: live("K1", A) }] }),
        violation: "unwitnessed-cover",
      },
      {
        name: "a cell proof that fails",
        build: () =>
          built(given([o("+", "K1", A)]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", A) },
            ],
          }),
        violation: "ground-not-live",
      },
      {
        name: "a cell proof at another boundary",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K", A)]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K", A) },
            ],
          }),
        violation: "type-mismatch",
      },
      {
        name: "a cell proof of another item",
        build: () =>
          built(given([o("+", "K1", A), o("+", "K2", C)]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", C) },
            ],
          }),
        violation: "type-mismatch",
      },
      {
        name: "cells that disagree on polarity",
        build: () =>
          built(given([o("+", "K1", A), o("-", "K2", A)]), {
            kind: "cover-glue",
            boundary: "K",
            item: A,
            cellProofs: [
              { cell: "K1", proof: live("K1", A) },
              { cell: "K2", proof: live("K2", A, { polarity: "-" }) },
            ],
          }),
        violation: "type-mismatch",
      },
    ],
  },

  "forall-intro": {
    accept: [
      {
        name: "an unconstrained universal whose body uses the eigenvariable",
        build: () =>
          built(given([["+", "B", P, "p"]]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P, { baseId: "p" })),
          }),
        expect: { boundary: "B", polarity: "+", item: forall("x", "H", implies(r("x"), P)), requiredBaseIds: ["p"], requiredGrounds: [g("B", P)] },
      },
      {
        name: "a constrained universal whose body uses the constraint",
        build: () =>
          built(given([]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: pos("x"),
            body: hyp("hc"),
            domainConstraint: pos("x"),
            constraintAssumpId: "hc",
          }),
        expect: { boundary: "B", polarity: "+", item: forall("x", "H", pos("x"), pos("x")), requiredBaseIds: [], requiredGrounds: [] },
      },
    ],
    reject: [
      {
        name: "an undefined boundary",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "Nowhere",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P)),
          }),
        violation: "invalid-boundary",
      },
      {
        name: "the empty boundary",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: BOT_BOUNDARY,
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P)),
          }),
        violation: "invalid-boundary",
      },
      {
        name: "an undefined domain",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "Nowhere",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P)),
          }),
        violation: "invalid-boundary",
      },
      {
        name: "the empty domain",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: BOT_BOUNDARY,
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P)),
          }),
        violation: "invalid-boundary",
      },
      {
        name: "a constraint without its assumption identifier",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P)),
            domainConstraint: pos("x"),
          }),
        violation: "type-mismatch",
      },
      {
        name: "an assumption identifier without a constraint",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", P)),
            constraintAssumpId: "hc",
          }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint identifier that shadows an open assumption",
        build: () =>
          built(
            given([]),
            intro("B", "hc", S, {
              kind: "forall-intro",
              boundary: "B",
              variable: "x",
              domain: "H",
              eigenvar: "e1",
              templateBody: pos("x"),
              body: hyp("hc"),
              domainConstraint: pos("x"),
              constraintAssumpId: "hc",
            }),
          ),
        violation: "shadowed-assumption",
      },
      {
        name: "an eigenvariable an enclosing forall-intro binds",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: forall("y", "H", implies(r("y"), P)),
            body: {
              kind: "forall-intro",
              boundary: "B",
              variable: "y",
              domain: "H",
              eigenvar: "e1",
              templateBody: implies(r("y"), P),
              body: intro("B", "hy", r("e1"), live("B", P)),
            },
          }),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "an eigenvariable that is a handle of Σ",
        build: () =>
          built(given([o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "h1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("h1"), live("B", P)),
          }),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "an eigenvariable an open assumption names",
        build: () =>
          built(
            given([o("+", "B", P)]),
            intro("B", "h0", r("e1"), {
              kind: "forall-intro",
              boundary: "B",
              variable: "x",
              domain: "H",
              eigenvar: "e1",
              templateBody: implies(r("x"), P),
              body: intro("B", "hx", r("e1"), live("B", P)),
            }),
          ),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "an eigenvariable the template names",
        build: () =>
          built(given([]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), r("e1")),
            body: intro("B", "hx", r("e1"), hyp("hx")),
          }),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "a body that fails",
        build: () =>
          built(given([]), { kind: "forall-intro", boundary: "B", variable: "x", domain: "H", eigenvar: "e1", templateBody: Q, body: live("B", Q) }),
        violation: "ground-not-live",
      },
      {
        name: "a negative body",
        build: () =>
          built(given([o("-", "B", N)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: N,
            body: live("B", N, { polarity: "-" }),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a body at another boundary",
        build: () =>
          built(given([o("+", "L", P)]), { kind: "forall-intro", boundary: "B", variable: "x", domain: "H", eigenvar: "e1", templateBody: P, body: live("L", P) }),
        violation: "type-mismatch",
      },
      {
        name: "a body that is no instance of the template",
        build: () =>
          built(given([o("+", "B", Q)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: implies(r("x"), P),
            body: intro("B", "hx", r("e1"), live("B", Q)),
          }),
        violation: "type-mismatch",
      },
    ],
  },

  "forall-elim": {
    accept: [
      {
        name: "an unconstrained universal at a handle of its domain",
        build: () => built(given([["+", "B", U, "u"]]), { kind: "forall-elim", universal: live("B", U, { baseId: "u" }), term: "h1" }),
        expect: { boundary: "B", polarity: "+", item: r("h1"), requiredBaseIds: ["u"], requiredGrounds: [g("B", U)] },
      },
      {
        name: "an assumed universal at an eigenvariable of its domain",
        build: () =>
          built(
            given([]),
            intro("B", "hu", U, {
              kind: "forall-intro",
              boundary: "B",
              variable: "y",
              domain: "H",
              eigenvar: "e1",
              templateBody: r("y"),
              body: { kind: "forall-elim", universal: hyp("hu"), term: "e1" },
            }),
          ),
        expect: { boundary: "B", polarity: "+", item: implies(U, forall("y", "H", r("y"))), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "a constrained universal with its constraint proof",
        build: () =>
          built(given([["+", "B", UC, "z_u"], ["+", "B", pos("h1"), "a_c"]]), {
            kind: "forall-elim",
            universal: live("B", UC, { baseId: "z_u" }),
            term: "h1",
            constraintProof: live("B", pos("h1"), { baseId: "a_c" }),
          }),
        expect: { boundary: "B", polarity: "+", item: r("h1"), requiredBaseIds: ["a_c", "z_u"], requiredGrounds: [g("B", UC), g("B", pos("h1"))] },
      },
      {
        name: "a derived universal and a derived constraint proof",
        build: () =>
          built(given([o("+", "B", UC), o("+", "B", pos("h1"))]), {
            kind: "forall-elim",
            universal: viaFlip("B", UC),
            term: "h1",
            constraintProof: viaFlip("B", pos("h1")),
          }),
        expect: {
          boundary: "B",
          polarity: "+",
          item: r("h1"),
          requiredBaseIds: [],
          requiredGrounds: [g("B", flip(UC), "-"), g("B", flip(pos("h1")), "-")],
        },
      },
      {
        // A proof built in JavaScript may carry an optional field set to undefined; the checker
        // reads it as absent.
        name: "an explicitly undefined constraint proof",
        build: () => built(given([["+", "B", U, "u"]]), { kind: "forall-elim", universal: live("B", U, { baseId: "u" }), term: "h1", constraintProof: undefined } as unknown as ProofNode),
        expect: { boundary: "B", polarity: "+", item: r("h1"), requiredBaseIds: ["u"], requiredGrounds: [g("B", U)] },
      },
    ],
    reject: [
      { name: "a universal that fails", build: () => built(given([]), { kind: "forall-elim", universal: live("B", U), term: "h1" }), violation: "ground-not-live" },
      {
        name: "a negative universal",
        build: () => built(given([o("-", "B", U)]), { kind: "forall-elim", universal: live("B", U, { polarity: "-" }), term: "h1" }),
        violation: "type-mismatch",
      },
      { name: "a premise that is no universal", build: () => built(given([o("+", "B", P)]), { kind: "forall-elim", universal: live("B", P), term: "h1" }), violation: "type-mismatch" },
      { name: "a term outside the domain", build: () => built(given([o("+", "B", U)]), { kind: "forall-elim", universal: live("B", U), term: "zz" }), violation: "inadmissible-term" },
      {
        name: "an eigenvariable of a coarser domain",
        build: () =>
          built(
            given([]),
            intro("B", "hu", U, {
              kind: "forall-intro",
              boundary: "B",
              variable: "y",
              domain: "B",
              eigenvar: "e1",
              templateBody: r("y"),
              body: { kind: "forall-elim", universal: hyp("hu"), term: "e1" },
            }),
          ),
        violation: "inadmissible-term",
      },
      {
        name: "a constrained universal without a constraint proof",
        build: () => built(given([o("+", "B", UC)]), { kind: "forall-elim", universal: live("B", UC), term: "h1" }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof that fails",
        build: () => built(given([o("+", "B", UC)]), { kind: "forall-elim", universal: live("B", UC), term: "h1", constraintProof: live("B", pos("h1")) }),
        violation: "ground-not-live",
      },
      {
        name: "a negative constraint proof",
        build: () =>
          built(given([o("+", "B", UC), o("-", "B", pos("h1"))]), {
            kind: "forall-elim",
            universal: live("B", UC),
            term: "h1",
            constraintProof: live("B", pos("h1"), { polarity: "-" }),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof at another boundary",
        build: () =>
          built(given([o("+", "B", UC), o("+", "L", pos("h1"))]), { kind: "forall-elim", universal: live("B", UC), term: "h1", constraintProof: live("L", pos("h1")) }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof for another term",
        build: () =>
          built(given([o("+", "B", UC), o("+", "B", pos("h2"))]), { kind: "forall-elim", universal: live("B", UC), term: "h1", constraintProof: live("B", pos("h2")) }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof for an unconstrained universal",
        build: () =>
          built(given([o("+", "B", U), o("+", "B", pos("h1"))]), { kind: "forall-elim", universal: live("B", U), term: "h1", constraintProof: live("B", pos("h1")) }),
        violation: "type-mismatch",
      },
    ],
  },

  "exists-intro": {
    accept: [
      {
        name: "an unconstrained existential from a witness",
        build: () =>
          built(given([["+", "B", r("h1"), "w"]]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1"), { baseId: "w" }),
          }),
        expect: { boundary: "B", polarity: "+", item: X, requiredBaseIds: ["w"], requiredGrounds: [g("B", r("h1"))] },
      },
      {
        name: "a constrained existential from a witness and its constraint proof",
        build: () =>
          built(given([["+", "B", r("h1"), "z_w"], ["+", "B", pos("h1"), "a_c"]]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1"), { baseId: "z_w" }),
            domainConstraint: pos("x"),
            constraintProof: live("B", pos("h1"), { baseId: "a_c" }),
          }),
        expect: { boundary: "B", polarity: "+", item: XC, requiredBaseIds: ["a_c", "z_w"], requiredGrounds: [g("B", r("h1")), g("B", pos("h1"))] },
      },
      {
        name: "a derived witness and a derived constraint proof",
        build: () =>
          built(given([o("+", "B", r("h1")), o("+", "B", pos("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: viaFlip("B", r("h1")),
            domainConstraint: pos("x"),
            constraintProof: viaFlip("B", pos("h1")),
          }),
        expect: {
          boundary: "B",
          polarity: "+",
          item: XC,
          requiredBaseIds: [],
          requiredGrounds: [g("B", flip(r("h1")), "-"), g("B", flip(pos("h1")), "-")],
        },
      },
    ],
    reject: [
      {
        name: "an undefined domain",
        build: () =>
          built(given([o("+", "B", r("h1"))]), { kind: "exists-intro", witnessTerm: "h1", variable: "x", domain: "Nowhere", templateBody: r("x"), witnessProof: live("B", r("h1")) }),
        violation: "invalid-boundary",
      },
      {
        name: "the empty domain",
        build: () =>
          built(given([o("+", "B", r("h1"))]), { kind: "exists-intro", witnessTerm: "h1", variable: "x", domain: BOT_BOUNDARY, templateBody: r("x"), witnessProof: live("B", r("h1")) }),
        violation: "invalid-boundary",
      },
      {
        name: "a constraint without a constraint proof",
        build: () =>
          built(given([o("+", "B", r("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1")),
            domainConstraint: pos("x"),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof without a constraint",
        build: () =>
          built(given([o("+", "B", r("h1")), o("+", "B", pos("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1")),
            constraintProof: live("B", pos("h1")),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a witness term outside the domain",
        build: () =>
          built(given([o("+", "B", r("zz"))]), { kind: "exists-intro", witnessTerm: "zz", variable: "x", domain: "H", templateBody: r("x"), witnessProof: live("B", r("zz")) }),
        violation: "inadmissible-term",
      },
      {
        name: "a witness proof that fails",
        build: () => built(given([]), { kind: "exists-intro", witnessTerm: "h1", variable: "x", domain: "H", templateBody: r("x"), witnessProof: live("B", r("h1")) }),
        violation: "ground-not-live",
      },
      {
        name: "a negative witness proof",
        build: () =>
          built(given([o("-", "B", r("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1"), { polarity: "-" }),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a witness proof for another term",
        build: () =>
          built(given([o("+", "B", r("h2"))]), { kind: "exists-intro", witnessTerm: "h1", variable: "x", domain: "H", templateBody: r("x"), witnessProof: live("B", r("h2")) }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof that fails",
        build: () =>
          built(given([o("+", "B", r("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1")),
            domainConstraint: pos("x"),
            constraintProof: live("B", pos("h1")),
          }),
        violation: "ground-not-live",
      },
      {
        name: "a negative constraint proof",
        build: () =>
          built(given([o("+", "B", r("h1")), o("-", "B", pos("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1")),
            domainConstraint: pos("x"),
            constraintProof: live("B", pos("h1"), { polarity: "-" }),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof at another boundary than the witness",
        build: () =>
          built(given([o("+", "B", r("h1")), o("+", "L", pos("h1"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1")),
            domainConstraint: pos("x"),
            constraintProof: live("L", pos("h1")),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint proof for another term",
        build: () =>
          built(given([o("+", "B", r("h1")), o("+", "B", pos("h2"))]), {
            kind: "exists-intro",
            witnessTerm: "h1",
            variable: "x",
            domain: "H",
            templateBody: r("x"),
            witnessProof: live("B", r("h1")),
            domainConstraint: pos("x"),
            constraintProof: live("B", pos("h2")),
          }),
        violation: "type-mismatch",
      },
    ],
  },

  "exists-elim": {
    accept: [
      {
        name: "a body that uses the witness assumption",
        build: () =>
          built(given([["+", "B", X, "z_ex"], ["+", "B", ALL_TO_P, "a_all"]]), {
            kind: "exists-elim",
            existential: live("B", X, { baseId: "z_ex" }),
            witnessVar: "w1",
            assumptionId: "hw",
            body: elim(hyp("hw"), { kind: "forall-elim", universal: live("B", ALL_TO_P, { baseId: "a_all" }), term: "w1" }),
          }),
        expect: { boundary: "B", polarity: "+", item: P, requiredBaseIds: ["a_all", "z_ex"], requiredGrounds: [g("B", X), g("B", ALL_TO_P)] },
      },
      {
        name: "a body that uses the constraint assumption",
        build: () =>
          built(given([o("+", "B", XC), o("+", "B", ALL_POS_TO_P)]), {
            kind: "exists-elim",
            existential: live("B", XC),
            witnessVar: "w1",
            assumptionId: "hw",
            constraintAssumpId: "hc",
            body: elim(hyp("hc"), { kind: "forall-elim", universal: live("B", ALL_POS_TO_P), term: "w1" }),
          }),
        expect: { boundary: "B", polarity: "+", item: P, requiredBaseIds: [], requiredGrounds: [g("B", XC), g("B", ALL_POS_TO_P)] },
      },
      {
        name: "a derived existential and a derived body",
        build: () =>
          built(given([o("+", "B", X), o("+", "B", P)]), { kind: "exists-elim", existential: viaFlip("B", X), witnessVar: "w1", assumptionId: "hw", body: viaFlip("B", P) }),
        expect: { boundary: "B", polarity: "+", item: P, requiredBaseIds: [], requiredGrounds: [g("B", flip(X), "-"), g("B", flip(P), "-")] },
      },
    ],
    reject: [
      {
        name: "an existential that fails",
        build: () => built(given([o("+", "B", P)]), { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: live("B", P) }),
        violation: "ground-not-live",
      },
      {
        name: "a negative existential",
        build: () =>
          built(given([o("-", "B", X), o("+", "B", P)]), {
            kind: "exists-elim",
            existential: live("B", X, { polarity: "-" }),
            witnessVar: "w1",
            assumptionId: "hw",
            body: live("B", P),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a premise that is no existential",
        build: () => built(given([o("+", "B", S), o("+", "B", P)]), { kind: "exists-elim", existential: live("B", S), witnessVar: "w1", assumptionId: "hw", body: live("B", P) }),
        violation: "type-mismatch",
      },
      {
        name: "a witness variable an enclosing forall-intro binds",
        build: () =>
          built(given([o("+", "B", X), o("+", "B", P)]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "w1",
            templateBody: P,
            body: { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: live("B", P) },
          }),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "a witness variable that is a handle of Σ",
        build: () =>
          built(given([o("+", "B", X), o("+", "B", P)]), { kind: "exists-elim", existential: live("B", X), witnessVar: "h1", assumptionId: "hw", body: live("B", P) }),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "a witness variable an open assumption names",
        build: () =>
          built(
            given([o("+", "B", X), o("+", "B", P)]),
            intro("B", "h0", r("w1"), { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: live("B", P) }),
          ),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "a witness variable the existential names",
        build: () =>
          built(given([o("+", "B", X), o("+", "B", P)]), { kind: "exists-elim", existential: live("B", X), witnessVar: "x", assumptionId: "hw", body: live("B", P) }),
        violation: "eigenvariable-not-fresh",
      },
      {
        name: "an assumption identifier that shadows an open one",
        build: () =>
          built(
            given([o("+", "B", X), o("+", "B", P)]),
            intro("B", "hw", S, { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: live("B", P) }),
          ),
        violation: "shadowed-assumption",
      },
      {
        name: "a constraint identifier for an unconstrained existential",
        build: () =>
          built(given([o("+", "B", X), o("+", "B", P)]), {
            kind: "exists-elim",
            existential: live("B", X),
            witnessVar: "w1",
            assumptionId: "hw",
            constraintAssumpId: "hc",
            body: live("B", P),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a constraint identifier that shadows an open assumption",
        build: () =>
          built(
            given([o("+", "B", XC), o("+", "B", P)]),
            intro("B", "hc", S, {
              kind: "exists-elim",
              existential: live("B", XC),
              witnessVar: "w1",
              assumptionId: "hw",
              constraintAssumpId: "hc",
              body: live("B", P),
            }),
          ),
        violation: "shadowed-assumption",
      },
      {
        name: "a constraint identifier equal to the witness assumption's",
        build: () =>
          built(given([o("+", "B", XC), o("+", "B", P)]), {
            kind: "exists-elim",
            existential: live("B", XC),
            witnessVar: "w1",
            assumptionId: "hw",
            constraintAssumpId: "hw",
            body: live("B", P),
          }),
        violation: "shadowed-assumption",
      },
      {
        name: "a body that fails",
        build: () => built(given([o("+", "B", X)]), { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: live("B", Q) }),
        violation: "ground-not-live",
      },
      {
        name: "a negative body",
        build: () =>
          built(given([o("+", "B", X), o("-", "B", N)]), {
            kind: "exists-elim",
            existential: live("B", X),
            witnessVar: "w1",
            assumptionId: "hw",
            body: live("B", N, { polarity: "-" }),
          }),
        violation: "type-mismatch",
      },
      {
        name: "a body at another boundary",
        build: () => built(given([o("+", "B", X), o("+", "L", P)]), { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: live("L", P) }),
        violation: "type-mismatch",
      },
      {
        name: "a witness variable that escapes into the conclusion",
        build: () => built(given([o("+", "B", X)]), { kind: "exists-elim", existential: live("B", X), witnessVar: "w1", assumptionId: "hw", body: hyp("hw") }),
        violation: "eigenvariable-escape",
      },
    ],
  },

  "flip-intro": {
    accept: [
      {
        name: "a positive premise",
        build: () => built(given([["+", "B", P, "p"]]), { kind: "flip-intro", inner: live("B", P, { baseId: "p" }) }),
        expect: { boundary: "B", polarity: "-", item: flip(P), requiredBaseIds: ["p"], requiredGrounds: [g("B", P)] },
      },
      {
        name: "a negative premise",
        build: () => built(given([o("-", "B", N)]), { kind: "flip-intro", inner: live("B", N, { polarity: "-" }) }),
        expect: { boundary: "B", polarity: "+", item: flip(N), requiredBaseIds: [], requiredGrounds: [g("B", N, "-")] },
      },
    ],
    reject: [{ name: "a premise that fails", build: () => built(given([]), { kind: "flip-intro", inner: live("B", P) }), violation: "ground-not-live" }],
  },

  "flip-elim": {
    accept: [
      {
        name: "a positive flipped premise",
        build: () => built(given([["+", "B", flip(P), "fp"]]), { kind: "flip-elim", inner: live("B", flip(P), { baseId: "fp" }) }),
        expect: { boundary: "B", polarity: "-", item: P, requiredBaseIds: ["fp"], requiredGrounds: [g("B", flip(P))] },
      },
      {
        name: "a negative flipped premise",
        build: () => built(given([o("+", "B", P)]), viaFlip("B", P)),
        expect: { boundary: "B", polarity: "+", item: P, requiredBaseIds: [], requiredGrounds: [g("B", flip(P), "-")] },
      },
    ],
    reject: [
      { name: "a premise that fails", build: () => built(given([]), { kind: "flip-elim", inner: live("B", flip(P)) }), violation: "ground-not-live" },
      { name: "a premise that is no flip", build: () => built(given([o("+", "B", P)]), { kind: "flip-elim", inner: live("B", P) }), violation: "type-mismatch" },
    ],
  },

  "equiv-refl": {
    accept: [
      {
        name: "a handle of the boundary",
        build: () => built(given([]), { kind: "equiv-refl", boundary: "B", term: "h1" }),
        expect: { boundary: "B", polarity: "+", item: equiv("B", "h1", "h1"), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "an eigenvariable of a domain that refines the boundary",
        build: () =>
          built(given([]), {
            kind: "forall-intro",
            boundary: "B",
            variable: "x",
            domain: "H",
            eigenvar: "e1",
            templateBody: equiv("B", "x", "x"),
            body: { kind: "equiv-refl", boundary: "B", term: "e1" },
          }),
        expect: { boundary: "B", polarity: "+", item: forall("x", "H", equiv("B", "x", "x")), requiredBaseIds: [], requiredGrounds: [] },
      },
    ],
    reject: [
      { name: "an undefined boundary", build: () => built(given([]), { kind: "equiv-refl", boundary: "Nowhere", term: "h1" }), violation: "invalid-boundary" },
      { name: "the empty boundary", build: () => built(given([]), { kind: "equiv-refl", boundary: BOT_BOUNDARY, term: "h1" }), violation: "invalid-boundary" },
      { name: "a term outside the boundary's domain", build: () => built(given([]), { kind: "equiv-refl", boundary: "H", term: "zz" }), violation: "inadmissible-term" },
    ],
  },

  "equiv-subst": {
    accept: [
      {
        name: "a left-to-right rewrite",
        build: () =>
          built(given([["+", "B", EQ, "z_eq"], ["+", "B", rel("h1", "zz"), "a_rel"]]), {
            kind: "equiv-subst",
            equivProof: live("B", EQ, { baseId: "z_eq" }),
            targetProof: live("B", rel("h1", "zz"), { baseId: "a_rel" }),
            direction: "left-to-right",
          }),
        expect: { boundary: "B", polarity: "+", item: rel("h2", "zz"), requiredBaseIds: ["a_rel", "z_eq"], requiredGrounds: [g("B", EQ), g("B", rel("h1", "zz"))] },
      },
      {
        name: "a right-to-left rewrite",
        build: () =>
          built(given([o("+", "B", equiv("B", "h2", "h1")), o("+", "B", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: live("B", equiv("B", "h2", "h1")),
            targetProof: live("B", rel("h1", "zz")),
            direction: "right-to-left",
          }),
        expect: { boundary: "B", polarity: "+", item: rel("h2", "zz"), requiredBaseIds: [], requiredGrounds: [g("B", equiv("B", "h2", "h1")), g("B", rel("h1", "zz"))] },
      },
      {
        name: "a negative target at a sub-boundary",
        build: () =>
          built(given([o("+", "B", EQ), o("-", "L", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: live("B", EQ),
            targetProof: live("L", rel("h1", "zz"), { polarity: "-" }),
            direction: "left-to-right",
          }),
        expect: { boundary: "L", polarity: "-", item: rel("h2", "zz"), requiredBaseIds: [], requiredGrounds: [g("B", EQ), g("L", rel("h1", "zz"), "-")] },
      },
      {
        name: "a named position among repeated occurrences",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", rel("h1", "h1"))]), {
            kind: "equiv-subst",
            equivProof: live("B", EQ),
            targetProof: live("B", rel("h1", "h1")),
            direction: "left-to-right",
            position: 1,
          }),
        expect: { boundary: "B", polarity: "+", item: rel("h1", "h2"), requiredBaseIds: [], requiredGrounds: [g("B", EQ), g("B", rel("h1", "h1"))] },
      },
      {
        name: "a derived equivalence and a derived target",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: viaFlip("B", EQ),
            targetProof: viaFlip("B", rel("h1", "zz")),
            direction: "left-to-right",
          }),
        expect: {
          boundary: "B",
          polarity: "+",
          item: rel("h2", "zz"),
          requiredBaseIds: [],
          requiredGrounds: [g("B", flip(EQ), "-"), g("B", flip(rel("h1", "zz")), "-")],
        },
      },
    ],
    reject: [
      {
        name: "an equivalence proof that fails",
        build: () =>
          built(given([o("+", "B", rel("h1", "zz"))]), { kind: "equiv-subst", equivProof: live("B", EQ), targetProof: live("B", rel("h1", "zz")), direction: "left-to-right" }),
        violation: "ground-not-live",
      },
      {
        name: "a target proof that fails",
        build: () => built(given([o("+", "B", EQ)]), { kind: "equiv-subst", equivProof: live("B", EQ), targetProof: live("B", rel("h1", "zz")), direction: "left-to-right" }),
        violation: "ground-not-live",
      },
      {
        name: "a negative equivalence",
        build: () =>
          built(given([o("-", "B", EQ), o("+", "B", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: live("B", EQ, { polarity: "-" }),
            targetProof: live("B", rel("h1", "zz")),
            direction: "left-to-right",
          }),
        violation: "type-mismatch",
      },
      {
        name: "an equivalence proof that is no equivalence",
        build: () =>
          built(given([o("+", "B", P), o("+", "B", rel("h1", "zz"))]), { kind: "equiv-subst", equivProof: live("B", P), targetProof: live("B", rel("h1", "zz")), direction: "left-to-right" }),
        violation: "type-mismatch",
      },
      {
        name: "a target that is not atomic",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", and(rel("h1", "zz"), P))]), {
            kind: "equiv-subst",
            equivProof: live("B", EQ),
            targetProof: live("B", and(rel("h1", "zz"), P)),
            direction: "left-to-right",
          }),
        violation: "type-mismatch",
      },
      {
        name: "premises over an unknown overlap",
        build: () =>
          built(given([o("+", "L", EQ), o("+", "H", rel("h1", "h2"))]), { kind: "equiv-subst", equivProof: live("L", EQ), targetProof: live("H", rel("h1", "h2")), direction: "left-to-right" }),
        violation: "unknown-meet",
      },
      {
        name: "premises on disjoint boundaries",
        build: () =>
          built(given([o("+", "D1", EQ), o("+", "D2", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: live("D1", EQ),
            targetProof: live("D2", rel("h1", "zz")),
            direction: "left-to-right",
          }),
        violation: "disjoint-meet",
      },
      {
        name: "an equivalence at a boundary outside its congruence boundary",
        build: () =>
          built(given([o("+", "B", equiv("L", "h1", "h2")), o("+", "B", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: live("B", equiv("L", "h1", "h2")),
            targetProof: live("B", rel("h1", "zz")),
            direction: "left-to-right",
          }),
        violation: "non-native-relation",
      },
      {
        name: "a relation not native to the congruence boundary",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", alien("h1", "zz"))]), { kind: "equiv-subst", equivProof: live("B", EQ), targetProof: live("B", alien("h1", "zz")), direction: "left-to-right" }),
        violation: "non-native-relation",
      },
      {
        name: "a rewrite to a handle no boundary declares",
        build: () => {
          const engine = given([o("+", "B", rel("h1", "zz"))]);
          engine.recordTheorem("B", "+", equiv("B", "h1", "nowhere"), "t_free"); // observations cannot name it
          return built(engine, {
            kind: "equiv-subst",
            equivProof: live("B", equiv("B", "h1", "nowhere")),
            targetProof: live("B", rel("h1", "zz")),
            direction: "left-to-right",
          });
        },
        violation: "type-mismatch",
      },
      {
        name: "a target without an occurrence of the rewritten handle",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", rel("h2", "zz"))]), { kind: "equiv-subst", equivProof: live("B", EQ), targetProof: live("B", rel("h2", "zz")), direction: "left-to-right" }),
        violation: "type-mismatch",
      },
      {
        name: "repeated occurrences without a position",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", rel("h1", "h1"))]), { kind: "equiv-subst", equivProof: live("B", EQ), targetProof: live("B", rel("h1", "h1")), direction: "left-to-right" }),
        violation: "type-mismatch",
      },
      {
        name: "a position that is no occurrence",
        build: () =>
          built(given([o("+", "B", EQ), o("+", "B", rel("h1", "zz"))]), {
            kind: "equiv-subst",
            equivProof: live("B", EQ),
            targetProof: live("B", rel("h1", "zz")),
            direction: "left-to-right",
            position: 1,
          }),
        violation: "type-mismatch",
      },
    ],
  },

  "refl-intro": {
    accept: [
      {
        name: "a record Live at an earlier stage",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", P, t) });
        },
        expect: { boundary: "B", polarity: "+", item: refl(0, "B", "+", P, T), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "a record absent at stage 0",
        build: () => {
          const { engine } = staged();
          return built(engine, { kind: "refl-intro", boundary: "L", reflItem: refl(0, "B", "+", P, 0) });
        },
        expect: { boundary: "L", polarity: "-", item: refl(0, "B", "+", P, 0), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "a record only evaluation derives",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(1, "B", "+", and(P, Q), t) });
        },
        expect: { boundary: "B", polarity: "+", item: refl(1, "B", "+", and(P, Q), T), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "a status that matches",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: reflStatus(0, t, "B", P, "Grounded") });
        },
        expect: { boundary: "B", polarity: "+", item: reflStatus(0, T, "B", P, "Grounded"), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "a status that does not match",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: reflStatus(0, t, "B", P, "Excluded") });
        },
        expect: { boundary: "B", polarity: "-", item: reflStatus(0, T, "B", P, "Excluded"), requiredBaseIds: [], requiredGrounds: [] },
      },
      {
        name: "the status of an Undetermined record",
        build: () => {
          const { engine, t } = stagedUndetermined();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: reflStatus(0, t, "B", P, "Collision") });
        },
        expect: { boundary: "B", polarity: "+", item: reflStatus(0, TU, "B", P, "Collision"), requiredBaseIds: [], requiredGrounds: [] },
      },
    ],
    reject: [
      {
        name: "an undefined boundary",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "Nowhere", reflItem: refl(0, "B", "+", P, t) });
        },
        violation: "invalid-boundary",
      },
      {
        name: "the empty boundary",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: BOT_BOUNDARY, reflItem: refl(0, "B", "+", P, t) });
        },
        violation: "invalid-boundary",
      },
      { name: "an item that is no reflection", build: () => built(staged().engine, { kind: "refl-intro", boundary: "B", reflItem: P }), violation: "type-mismatch" },
      { name: "a stage-less reflection", build: () => built(staged().engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", P) }), violation: "type-mismatch" },
      { name: "a negative stage", build: () => built(staged().engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", P, -1) }), violation: "stratification-violation" },
      { name: "a fractional stage", build: () => built(staged().engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", P, 0.5) }), violation: "stratification-violation" },
      {
        name: "the current stage",
        build: () => {
          const { engine } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", P, engine.stage) });
        },
        violation: "stratification-violation",
      },
      {
        name: "a level below the reflected item's",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", refl(0, "B", "+", P, 0), t) });
        },
        violation: "stratification-violation",
      },
      {
        name: "a fractional level",
        build: () => {
          const { engine, t } = staged();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0.5, "B", "+", P, t) });
        },
        violation: "stratification-violation",
      },
      {
        name: "a target boundary declared after the reflected stage",
        build: () => {
          const { engine, t } = staged();
          engine.boundaries.defineBoundary("Late");
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "Late", "+", P, t) });
        },
        violation: "invalid-boundary",
      },
      {
        name: "an Undetermined record",
        build: () => {
          const { engine, t } = stagedUndetermined();
          return built(engine, { kind: "refl-intro", boundary: "B", reflItem: refl(0, "B", "+", P, t) });
        },
        violation: "ground-not-live",
      },
    ],
  },

  "ex-falso-bottom": {
    accept: [
      {
        name: "⊥ under UL-Intuitionistic",
        build: () => built(given([["+", "B", NB, "na"]], { monotoneOnly: true }), exFalsoProof(elim(hyp("h"), live("B", NB, { baseId: "na" }))), "UL-Intuitionistic"),
        expect: { boundary: "B", polarity: "+", item: implies(A, C), requiredBaseIds: ["na"], requiredGrounds: [g("B", NB)] },
      },
      {
        name: "a derived proof of ⊥",
        build: () => built(given([o("+", "B", NB)], { monotoneOnly: true }), exFalsoProof(elim(hyp("h"), viaFlip("B", NB))), "UL-Intuitionistic"),
        expect: { boundary: "B", polarity: "+", item: implies(A, C), requiredBaseIds: [], requiredGrounds: [g("B", flip(NB), "-")] },
      },
    ],
    reject: [
      {
        name: "UL-Core",
        build: () => built(given([o("+", "B", NB)], { monotoneOnly: true }), exFalsoProof(elim(hyp("h"), live("B", NB))), "UL-Core"),
        violation: "ex-falso-disallowed",
      },
      {
        name: "UL-Minimal",
        build: () => built(given([o("+", "B", NB)], { monotoneOnly: true }), exFalsoProof(elim(hyp("h"), live("B", NB))), "UL-Minimal"),
        violation: "ex-falso-disallowed",
      },
      {
        name: "a proof of ⊥ that fails",
        build: () => built(given([], { monotoneOnly: true }), exFalsoProof(elim(hyp("h"), live("B", NB))), "UL-Intuitionistic"),
        violation: "ground-not-live",
      },
      {
        name: "a negative ⊥",
        build: () =>
          built(given([o("-", "B", bottom())], { monotoneOnly: true }), { kind: "ex-falso-bottom", bottomProof: live("B", bottom(), { polarity: "-" }), target: C }, "UL-Intuitionistic"),
        violation: "type-mismatch",
      },
      {
        name: "a premise that is not ⊥",
        build: () => built(given([o("+", "B", P)], { monotoneOnly: true }), { kind: "ex-falso-bottom", bottomProof: live("B", P), target: C }, "UL-Intuitionistic"),
        violation: "type-mismatch",
      },
    ],
  },
};

const RULE_KINDS: ReadonlySet<string> = new Set(Object.keys(RULE_CASES));

function test_every_proof_rule_accepts_its_proofs_and_rejects_each_near_miss(): void {
  for (const [kind, cases] of Object.entries(RULE_CASES) as [ProofNode["kind"], RuleCases][]) {
    for (const c of cases.accept) {
      test(`${kind} accepts ${c.name}`, () => checkAccept(kind, c, RULE_KINDS));
    }
    for (const c of cases.reject) {
      test(`${kind} rejects ${c.name}`, () => checkReject(kind, c, RULE_KINDS));
    }
  }
}

function test_mode_precondition_comes_before_every_rule(): void {
  // UL-Minimal and UL-Intuitionistic require a monotone Σ without collisions; UL-Core does not.
  const proof = live("B", P);
  const plain = given([o("+", "B", P)]);
  const collided = given([o("+", "B", P), o("-", "B", Q), o("+", "B", Q)], { monotoneOnly: true });
  const clean = given([o("+", "B", P)], { monotoneOnly: true });
  const outcome = (e: InquiryEngine, mode: DeductionMode): string => {
    const res = verifyDerivation(e, proof, mode);
    return res.ok ? "accepted" : res.violation;
  };
  assert.equal(outcome(plain, "UL-Core"), "accepted");
  assert.equal(outcome(plain, "UL-Minimal"), "mode-precondition");
  assert.equal(outcome(plain, "UL-Intuitionistic"), "mode-precondition");
  assert.equal(outcome(collided, "UL-Core"), "accepted");
  assert.equal(outcome(collided, "UL-Minimal"), "mode-precondition");
  assert.equal(outcome(collided, "UL-Intuitionistic"), "mode-precondition");
  assert.equal(outcome(clean, "UL-Minimal"), "accepted");
  assert.equal(outcome(clean, "UL-Intuitionistic"), "accepted");
}

function test_admission_records_only_what_the_checker_accepts(): void {
  // A rejected proof is reported as the checker reports it and records nothing.
  const e = given([o("+", "B", P)]);
  const stage = e.stage;
  const rejected = admitVerifiedDerivation(e, live("B", Q), "thm");
  assert.equal(rejected.ok ? "admitted" : rejected.violation, "ground-not-live");
  assert.equal(e.stage, stage);

  // An ex-falso step nested in a cover cell keeps a verified UL-Intuitionistic result out of Σ.
  const m = given([o("+", "K1", NB), o("+", "K2", NB)], { monotoneOnly: true });
  const cell = (c: string): ProofNode => ({ kind: "ex-falso-bottom", bottomProof: elim(hyp("h", c), live(c, NB)), target: C });
  const proof = intro("K", "h", A, {
    kind: "cover-glue",
    boundary: "K",
    item: C,
    cellProofs: [
      { cell: "K1", proof: cell("K1") },
      { cell: "K2", proof: cell("K2") },
    ],
  });
  assert.equal(verifyDerivation(m, proof, "UL-Intuitionistic").ok, true);
  const mStage = m.stage;
  const efq = admitVerifiedDerivation(m, proof, "thm", "UL-Intuitionistic");
  assert.equal(efq.ok ? "admitted" : efq.violation, "mode-only-rule");
  assert.equal(m.stage, mStage);
}

test_every_proof_rule_accepts_its_proofs_and_rejects_each_near_miss();
test("verifyDerivation checks the mode precondition before any rule", test_mode_precondition_comes_before_every_rule);
test("admission records only what the checker accepts", test_admission_records_only_what_the_checker_accepts);
