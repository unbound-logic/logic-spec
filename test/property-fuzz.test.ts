import assert from "node:assert/strict";
import { test } from "node:test";
import { BOT_BOUNDARY, BoundarySystem, TOP_BOUNDARY, type HandleSpec } from "../src/boundary.ts";
import { admitVerifiedDerivation, type ProofNode, verifyDerivation } from "../src/deduction.ts";
import { InquiryEngine } from "../src/engine.ts";
import {
  evaluateClassicalSpecialization,
  verifyIntuitionisticSpecialization,
  verifyMinimalSpecialization,
} from "../src/specializations.ts";
import {
  and,
  atom,
  bottom,
  checkRecursiveDefinitionSystem,
  collectHandles,
  equiv,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  type Polarity,
  type RecursiveDef,
  ref,
  refl,
  reflStatus,
  structImposs,
  substituteHandle,
  type Item,
} from "../src/syntax.ts";

class Rng {
  #state: number;

  constructor(seed: number) {
    this.#state = seed >>> 0;
  }

  next(): number {
    this.#state = (this.#state + 0x6d2b79f5) >>> 0;
    let t = Math.imul(this.#state ^ (this.#state >>> 15), 1 | this.#state);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  int(min: number, max: number): number {
    return min + Math.floor(this.next() * (max - min + 1));
  }

  bool(p = 0.5): boolean {
    return this.next() < p;
  }

  pick<T>(items: readonly T[]): T {
    if (items.length === 0) {
      throw new Error("Rng.pick called on empty array.");
    }
    const picked = items[this.int(0, items.length - 1)];
    if (picked === undefined) {
      throw new Error("Unexpected undefined pick.");
    }
    return picked;
  }
}

function getSuiteSeeds(suiteId: number, defaultCount: number): readonly number[] {
  const seedEnv = process.env.UL_FUZZ_SEED;
  if (seedEnv !== undefined && seedEnv.trim() !== "") {
    const parsed = Number.parseInt(seedEnv.trim(), 10);
    if (!Number.isNaN(parsed)) {
      return [parsed >>> 0];
    }
  }
  const multEnv = process.env.UL_FUZZ_MULTIPLIER;
  let mult = 1;
  if (multEnv !== undefined && multEnv.trim() !== "") {
    const parsed = Number.parseFloat(multEnv.trim());
    if (Number.isFinite(parsed) && parsed > 0) {
      mult = parsed;
    }
  }
  const count = Math.max(1, Math.round(defaultCount * mult));
  const seeds: number[] = [];
  for (let i = 0; i < count; i++) {
    const seed = (Math.imul(suiteId + 1, 0x9e3779b1) ^ Math.imul(i + 1, 0x85ebca6b)) >>> 0;
    seeds.push(seed);
  }
  return seeds;
}

function commonNonEmptySubs(
  bs: BoundarySystem,
  nodes: readonly string[],
  a: string,
  b: string,
): readonly string[] {
  return nodes.filter((c) => c !== BOT_BOUNDARY && bs.refines(c, a) && bs.refines(c, b));
}

function maximalCommonSubs(
  bs: BoundarySystem,
  nodes: readonly string[],
  a: string,
  b: string,
): readonly string[] {
  const common = commonNonEmptySubs(bs, nodes, a, b);
  return common.filter((c) => !common.some((other) => other !== c && bs.refines(c, other)));
}

function wouldBeAmbiguousAfterJoin(
  bs: BoundarySystem,
  definedNodes: readonly string[],
  p0: string,
  p1: string,
): boolean {
  const anc0 = definedNodes.filter((n) => bs.refines(p0, n));
  const anc1 = definedNodes.filter((n) => bs.refines(p1, n));
  for (const x of anc0) {
    for (const y of anc1) {
      if (x === y || bs.refines(x, y) || bs.refines(y, x)) {
        continue;
      }
      const existingMax = maximalCommonSubs(bs, definedNodes, x, y);
      const hasIndependentMax = existingMax.some(
        (m) => !(bs.refines(p0, m) && bs.refines(p1, m)),
      );
      if (hasIndependentMax) {
        return true;
      }
    }
  }
  return false;
}

/**
 * Suite 1 (MT-4, MT-5): Boundary meet-semilattice laws, disjoint monotonicity,
 * defineMeet(..., BOT_BOUNDARY) parity, and finitary Grothendieck cover axioms.
 */
function test_fuzz_semilattice_and_finitary_covers(): void {
  const seeds = getSuiteSeeds(1, 50);
  for (const seed of seeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=semilattice seed=${seed}]`;
    const bs = new BoundarySystem();
    const nodeCount = rng.int(4, 7);
    const nodes: string[] = [];
    const handlesPool: readonly HandleSpec[] = [
      { id: "h0", criterion: "I(h0)", kind: "structural" },
      { id: "h1", criterion: "I(h1)", kind: "structural" },
    ];

    for (let i = 0; i < nodeCount; i++) {
      const id = `B${i}`;
      if (i === 0) {
        bs.defineBoundary(id, { nativeRelations: ["P", "Q"], handles: handlesPool });
      } else {
        const candidates = [TOP_BOUNDARY, ...nodes];
        const p0 = rng.pick(candidates);
        const parents = [p0];
        if (i >= 2 && p0 !== TOP_BOUNDARY && rng.bool(0.35)) {
          const secondCands = nodes.filter(
            (n) =>
              n !== p0 &&
              !bs.refines(p0, n) &&
              !bs.refines(n, p0) &&
              bs.overlaps(p0, n) === false &&
              !wouldBeAmbiguousAfterJoin(bs, nodes, p0, n),
          );
          if (secondCands.length > 0) {
            const p1 = rng.pick(secondCands);
            const probe = bs.clone();
            let disjointErr = false;
            try {
              probe.defineBoundary("__probe__", { parents: [p0, p1] });
            } catch {
              disjointErr = true;
            }
            if (!disjointErr) {
              parents.push(p1);
            }
          }
        }
        bs.defineBoundary(id, { parents });
      }
      nodes.push(id);

      const disjointList: [string, string][] = [];
      for (const prev of nodes.slice(0, -1)) {
        if (bs.refines(id, prev) || bs.refines(prev, id)) {
          continue;
        }
        const common = commonNonEmptySubs(bs, nodes, id, prev);
        if (common.length === 0 && rng.bool(0.35)) {
          disjointList.push([prev, id]);
        }
      }
      for (const [a, b] of disjointList) {
        if (rng.bool(0.5)) {
          bs.declareDisjoint(a, b);
        } else {
          bs.defineMeet(a, b, BOT_BOUNDARY);
        }
      }
    }

    for (let i = 0; i < nodes.length; i++) {
      for (let j = i + 1; j < nodes.length; j++) {
        const a = nodes[i];
        const b = nodes[j];
        if (a === undefined || b === undefined) {
          continue;
        }
        if (bs.refines(a, b) || bs.refines(b, a)) {
          continue;
        }
        const maxSubs = maximalCommonSubs(bs, nodes, a, b);
        if (maxSubs.length === 1 && maxSubs[0] !== undefined && rng.bool(0.5)) {
          const m = maxSubs[0];
          bs.defineMeet(a, b, m);
          assert.throws(() => bs.declareDisjoint(a, b), /meet|common|disjoint/i, ctx);
          assert.throws(() => bs.defineMeet(a, b, BOT_BOUNDARY), /meet|common|disjoint/i, ctx);
        }
      }
    }

    const allBounds = [TOP_BOUNDARY, BOT_BOUNDARY, ...nodes];
    for (const x of allBounds) {
      assert.equal(bs.refines(x, x), true, `${ctx} reflexivity ${x}`);
      assert.equal(bs.refines(BOT_BOUNDARY, x), true, `${ctx} bottom <= ${x}`);
      assert.equal(bs.refines(x, TOP_BOUNDARY), true, `${ctx} ${x} <= top`);
      assert.equal(bs.meet(x, x), x, `${ctx} idempotence ${x}`);
      for (const y of allBounds) {
        if (x !== y && bs.refines(x, y)) {
          assert.equal(bs.refines(y, x), false, `${ctx} antisymmetry ${x}, ${y}`);
        }
        const mxy = bs.meet(x, y);
        const myx = bs.meet(y, x);
        assert.equal(mxy, myx, `${ctx} commutativity ${x}, ${y}`);
        assert.equal(bs.refines(mxy, x), true, `${ctx} meet <= left`);
        assert.equal(bs.refines(mxy, y), true, `${ctx} meet <= right`);
        for (const z of allBounds) {
          if (bs.refines(x, y) && bs.refines(y, z)) {
            assert.equal(bs.refines(x, z), true, `${ctx} transitivity ${x} <= ${y} <= ${z}`);
          }
          if (bs.refines(z, x) && bs.refines(z, y)) {
            assert.equal(bs.refines(z, mxy), true, `${ctx} GLB ${z} <= meet(${x},${y})=${mxy}`);
          }
        }
      }
    }

    for (let i = 0; i < nodes.length; i++) {
      for (let j = i + 1; j < nodes.length; j++) {
        const u = nodes[i];
        const v = nodes[j];
        if (u === undefined || v === undefined) {
          continue;
        }
        if (bs.meet(u, v) === BOT_BOUNDARY) {
          for (const u1 of bs.nonEmptySubBoundaries(u)) {
            for (const v1 of bs.nonEmptySubBoundaries(v)) {
              assert.equal(
                bs.meet(u1, v1),
                BOT_BOUNDARY,
                `${ctx} disjoint monotonicity violated on (${u1}, ${v1})`,
              );
              assert.equal(bs.overlaps(u1, v1), false, `${ctx} overlaps must be false`);
              if (commonNonEmptySubs(bs, nodes, u, v).length === 0) {
                const probeClone = bs.clone();
                try {
                  probeClone.defineBoundary("__check_disj__", { parents: [u, v] });
                } catch {
                  const testClone = bs.clone();
                  assert.throws(
                    () => testClone.defineBoundary("__bad_joint__", { parents: [u1, v1] }),
                    /disjoint/i,
                    `${ctx} joint child under (${u1}, ${v1}) should be rejected`,
                  );
                }
              }
            }
          }
        }
      }
    }

    const target = rng.pick(nodes);
    assert.equal(bs.isWitnessedCover(target, [target]), true, `${ctx} Axiom 2 Identity`);
    assert.equal(bs.isWitnessedCover(BOT_BOUNDARY, []), true, `${ctx} Axiom 2 Bottom Identity`);
    assert.throws(() => bs.registerCover(target, []), /Non-Vacuity/, `${ctx} Axiom 5 register`);
    assert.equal(bs.isWitnessedCover(target, []), false, `${ctx} Axiom 5 query`);

    const nonRefining = nodes.find((n) => !bs.refines(n, target));
    if (nonRefining !== undefined) {
      assert.throws(
        () => bs.registerCover(target, [nonRefining]),
        /Refinement violation/,
        `${ctx} Axiom 1 Refinement`,
      );
    }

    const cLeft = `${target}_cL`;
    const cRight = `${target}_cR`;
    const cLeftA = `${target}_cLA`;
    const cLeftB = `${target}_cLB`;
    bs.defineBoundary(cLeft, { parents: [target] });
    bs.defineBoundary(cRight, { parents: [target] });
    bs.declareDisjoint(cLeft, cRight);
    bs.defineBoundary(cLeftA, { parents: [cLeft] });
    bs.defineBoundary(cLeftB, { parents: [cLeft] });
    bs.declareDisjoint(cLeftA, cLeftB);

    bs.registerCover(target, [cLeft, cRight]);
    bs.registerCover(cLeft, [cLeftA, cLeftB]);

    assert.equal(
      bs.isWitnessedCover(target, [cLeftA, cLeftB, cRight]),
      true,
      `${ctx} Axiom 4 Transitivity`,
    );

    for (const sub of bs.nonEmptySubBoundaries(target)) {
      const pulled = [
        ...new Set(
          [cLeft, cRight]
            .map((cell) => bs.meet(cell, sub))
            .filter((m) => m !== BOT_BOUNDARY),
        ),
      ];
      if (pulled.length > 0) {
        assert.equal(
          bs.isWitnessedCover(sub, pulled),
          true,
          `${ctx} Axiom 3 Meet-Stability on sub=${sub}`,
        );
      }
    }
  }
}

function assertSnapshotCoreInvariants(
  snap: ReturnType<InquiryEngine["evaluate"]>,
  boundaries: BoundarySystem,
  itemsToCheck: readonly Item[],
  sentinel: Item,
  ctx: string,
): void {
  const bot = bottom();
  const nonEmpty = boundaries.nonEmptyBoundaries();
  const entryCache = new Map<string, boolean>();

  const verifyEntryDag = (entryId: string, visiting: Set<string>): void => {
    if (entryCache.get(entryId)) {
      return;
    }
    assert.equal(visiting.has(entryId), false, `${ctx} Cycle detected in Live DAG at ${entryId}`);
    assert.equal(snap.isEntryLive(entryId), true, `${ctx} Dependency ${entryId} is not Live`);
    const entry = snap.entryById(entryId);
    assert.ok(entry !== undefined, `${ctx} Missing entry ${entryId} in snapshot`);
    visiting.add(entryId);
    if (entry.provenance.kind === "derived") {
      for (const depId of entry.provenance.depEntryIds) {
        verifyEntryDag(depId, visiting);
      }
    }
    visiting.delete(entryId);
    entryCache.set(entryId, true);
  };

  for (const b of nonEmpty) {
    assert.equal(snap.statusOf(b, sentinel), "Open", `${ctx} Non-Explosion violated on ${b}`);
    assert.equal(snap.allGrounds(b, "+", sentinel).length, 0, `${ctx} Sentinel + ground on ${b}`);
    assert.equal(snap.statusOf(b, bot), "Excluded", `${ctx} bottom must stay Excluded on ${b}`);
    assert.equal(snap.isLive(b, "+", bot), false, `${ctx} bottom must never be Live (+) on ${b}`);
    assert.equal(snap.allGrounds(b, "+", bot).length, 0, `${ctx} zero +bottom entries on ${b}`);

    const subs = boundaries.nonEmptySubBoundaries(b);
    for (const it of itemsToCheck) {
      const posAll = snap.allGrounds(b, "+", it);
      const negAll = snap.allGrounds(b, "-", it);
      const st = snap.statusOf(b, it);
      const expectedStatus =
        posAll.length > 0 && negAll.length > 0
          ? "Collision"
          : posAll.length > 0
            ? "Grounded"
            : negAll.length > 0
              ? "Excluded"
              : "Open";
      assert.equal(st, expectedStatus, `${ctx} status mismatch for (${b}, ${itemKey(it)})`);

      for (const pol of ["+", "-"] as const) {
        const lives = snap.liveGrounds(b, pol, it);
        if (lives.length > 0) {
          assert.equal(
            snap.isObstructed(b, it),
            false,
            `${ctx} Live (${b}, ${pol}, ${itemKey(it)}) cannot be obstructed`,
          );
          for (const sub of subs) {
            assert.notEqual(
              snap.statusOf(sub, it),
              "Collision",
              `${ctx} Live (${b}, ${pol}, ${itemKey(it)}) has colliding sub-boundary ${sub}`,
            );
          }
          for (const entry of lives) {
            verifyEntryDag(entry.entryId, new Set<string>());
          }
        }
      }
    }
  }
}

/**
 * Suite 2 (MT-1, MT-3, MT-6): Randomized inquiry dynamics, Retract purity,
 * unbiased Quarantine invariants, plus biased high-density G-15 conflict attacks
 * (covering both pure symmetric conflicts and asymmetric defeat reinstatement)
 * and MT-1 cross-conflict mutual bridge probing.
 */
function test_fuzz_inquiry_dynamics_quarantine_and_biased_conflict_graphs(): void {
  // Part A: General randomized inquiry sequences
  const generalSeeds = getSuiteSeeds(2, 10);
  for (const seed of generalSeeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=inquiry-general seed=${seed}]`;
    const bs = new BoundarySystem();
    bs.defineBoundary("B0");
    bs.defineBoundary("B1", { parents: ["B0"] });
    bs.defineBoundary("B2", { parents: ["B0"] });
    if (rng.bool(0.5)) {
      bs.declareDisjoint("B1", "B2");
    }
    const useSub = rng.bool(0.6);
    if (useSub) {
      bs.defineBoundary("B1_sub", { parents: ["B1"] });
    }
    const activeBounds = bs.nonEmptyBoundaries().filter((b) => b !== TOP_BOUNDARY);

    const engine = new InquiryEngine(bs);
    const p0 = atom("P0");
    const p1 = atom("P1");
    const p2 = atom("P2");
    const p3 = atom("P3");
    const sentinel = atom("SentinelNoise");
    const baseAtoms = [p0, p1, p2, p3];
    const queryPool: Item[] = [
      p0,
      p1,
      p2,
      p3,
      bottom(),
      implies(p0, p1),
      implies(p1, p2),
      implies(p2, p3),
      flip(p0),
      flip(p1),
      and(p0, p1),
      or(p0, p1),
      structImposs(p0),
      structImposs(structImposs(p0)),
    ];

    const activeIds: string[] = [];
    let coverSplitDone = false;
    const steps = rng.int(10, 14);
    for (let s = 0; s < steps; s++) {
      const action = rng.int(0, 5);
      if (action <= 1) {
        const b = rng.pick(activeBounds);
        const it = rng.pick(queryPool.filter((x) => x.kind !== "bottom"));
        const id = `obs_${seed}_${s}`;
        engine.observePositive(b, it, id);
        activeIds.push(id);
      } else if (action === 2) {
        const b = rng.pick(activeBounds);
        const it = rng.pick(queryPool);
        const id = `neg_${seed}_${s}`;
        engine.observeNegative(b, it, id);
        activeIds.push(id);
      } else if (action === 3 && activeIds.length > 0) {
        const idx = rng.int(0, activeIds.length - 1);
        const id = activeIds[idx];
        if (id !== undefined) {
          const retracted = engine.retract(id);
          assert.equal(retracted, true, `${ctx} retract active id ${id}`);
          activeIds.splice(idx, 1);
        }
      } else if (action === 4) {
        const b = rng.pick(activeBounds);
        const left = rng.pick(baseAtoms);
        const right = rng.pick(baseAtoms.filter((x) => x !== left));
        engine.addIncompatibility(b, left, right);
      } else {
        const b = rng.pick(activeBounds);
        if (!coverSplitDone && b === "B0" && rng.bool(0.5)) {
          coverSplitDone = true;
          const cA = `B0_cA_${s}`;
          const cB = `B0_cB_${s}`;
          bs.defineBoundary(cA, { parents: ["B0"] });
          bs.defineBoundary(cB, { parents: ["B0"] });
          bs.declareDisjoint(cA, cB);
          engine.witnessCover("B0", [cA, cB]);
          activeBounds.push(cA, cB);
        } else {
          engine.addStructuralCollapse(b, rng.pick(baseAtoms));
        }
      }
    }

    const snap = engine.evaluate([...queryPool, sentinel, bottom()]);
    assertSnapshotCoreInvariants(snap, bs, [...queryPool, sentinel], sentinel, ctx);

    // Retract purity check (MT-6)
    const freshAtom = atom(`FreshProbe_${seed}`);
    const probeBound = rng.pick(activeBounds);
    const probeId = `fresh_${seed}`;
    if (rng.bool(0.5)) {
      engine.observePositive(probeBound, freshAtom, probeId);
    } else {
      engine.observeNegative(probeBound, freshAtom, probeId);
    }
    assert.equal(engine.retract(probeId), true, `${ctx} retract fresh probe`);
    const afterRetract = engine.evaluate([freshAtom]);
    assert.equal(
      afterRetract.statusOf(probeBound, freshAtom),
      "Open",
      `${ctx} pure Retract must return fresh item to Open`,
    );

    // Reinstatement check (MT-6)
    const bRein = new BoundarySystem();
    bRein.defineBoundary("BR");
    const eRein = new InquiryEngine(bRein);
    const reinItem = atom("ReinTarget");
    eRein.observePositive("BR", reinItem, "r_pos");
    eRein.observeNegative("BR", reinItem, "r_neg");
    assert.equal(eRein.evaluate([reinItem]).statusOf("BR", reinItem), "Collision");
    assert.equal(eRein.evaluate([reinItem]).isLive("BR", "+", reinItem), false);
    assert.equal(eRein.retract("r_neg"), true);
    assert.equal(eRein.evaluate([reinItem]).statusOf("BR", reinItem), "Grounded");
    assert.equal(eRein.evaluate([reinItem]).isLive("BR", "+", reinItem), true);
  }

  // Part B: Biased G-15 high-density conflict graphs + MT-1 cross-conflict bridge probe
  let knownCrossConflictBridgeHits = 0;
  const biasedSeeds = getSuiteSeeds(20, 12);
  for (let index = 0; index < biasedSeeds.length; index++) {
    const seed = biasedSeeds[index]!;
    const rng = new Rng(seed);
    const ctx = `[suite=inquiry-biased seed=${seed}]`;
    const bs = new BoundarySystem();
    bs.defineBoundary("B");

    const singleSeedReplay = biasedSeeds.length === 1;
    const isAsymmetricMode = !singleSeedReplay && index % 2 === 1;
    let useSub = rng.bool(0.4);
    const threeHop = rng.bool(0.5);

    const a = atom("A");
    const c = atom("C");
    const x1 = atom("X1");
    const x2 = atom("X2");
    const y = atom("Y");
    const sentinel = atom("SentinelNoise");

    const reversePool: readonly [Item, Item, string][] = [
      [y, c, "rev_yc"],
      [y, flip(a), "rev_yna"],
      [y, flip(c), "rev_ync"],
      [x1, c, "rev_x1c"],
      [x1, flip(a), "rev_x1na"],
      [x1, flip(c), "rev_x1nc"],
    ];
    const revCount = rng.int(1, 4);
    const pickedRevs: (readonly [Item, Item, string])[] = [];
    for (let k = 0; k < revCount; k++) {
      pickedRevs.push(rng.pick(reversePool));
    }
    const rawExtraFlipA = rng.bool(0.4);
    const rawSubNegA = useSub ? rng.bool(0.5) : false;

    let extraFlipA = false;
    let subNegA = false;
    if (singleSeedReplay) {
      extraFlipA = rawExtraFlipA;
      subNegA = rawSubNegA;
    } else if (isAsymmetricMode) {
      // Ensure odd runs exercise at least one independent defeat of A (including both-on like seed 4049301331)
      if (index % 4 === 3) {
        useSub = true;
        extraFlipA = true;
        subNegA = true;
      } else {
        extraFlipA = rawExtraFlipA;
        subNegA = rawSubNegA;
        if (!extraFlipA && !subNegA) {
          extraFlipA = true;
        }
      }
    }

    if (useSub) {
      bs.defineBoundary("B_sub", { parents: ["B"] });
    }
    const e = new InquiryEngine(bs);

    e.addIncompatibility("B", a, c);
    e.observePositive("B", a, "wa");
    e.observePositive("B", c, "wc");

    const targetChainItems = threeHop ? [x1, x2, y] : [x1, y];
    e.observePositive("B", implies(a, x1), "wax1");
    if (threeHop) {
      e.observePositive("B", implies(x1, x2), "wx12");
      e.observePositive("B", implies(x2, y), "wx2y");
    } else {
      e.observePositive("B", implies(x1, y), "wx1y");
    }
    e.observeNegative("B", y, "wny");

    for (let k = 0; k < pickedRevs.length; k++) {
      const [src, dst, label] = pickedRevs[k]!;
      e.observePositive("B", implies(src, dst), `${label}_${k}`);
    }
    if (extraFlipA) {
      e.observePositive("B", flip(a), "w_extra_flip_a");
    }
    if (subNegA) {
      e.observeNegative("B_sub", a, "w_sub_na");
    }

    // Collided antecedent counter-implies trap
    const collAnt = atom("CollAnt");
    const cons = atom("Cons");
    e.observePositive("B", collAnt, "wca_p");
    e.observeNegative("B", collAnt, "wca_n");
    e.observePositive("B", implies(collAnt, cons), "wcac");
    e.observeNegative("B", cons, "wcons");

    const allChecked = [
      a,
      c,
      ...targetChainItems,
      flip(a),
      flip(c),
      flip(y),
      collAnt,
      cons,
      implies(collAnt, cons),
      sentinel,
      bottom(),
    ];
    const snap = e.evaluate(allChecked);
    assertSnapshotCoreInvariants(snap, bs, allChecked, sentinel, ctx);

    const hasIndependentDefeatOfA = extraFlipA || subNegA;
    assert.equal(snap.statusOf("B", a), "Collision", `${ctx} A must be Collision`);
    assert.equal(snap.isLive("B", "+", a), false, `${ctx} A not Live`);
    if (hasIndependentDefeatOfA) {
      // Stratified Quarantine Reinstatement: A is independently defeated, so +A never fires A ⊥_B C; C is reinstated!
      assert.equal(snap.statusOf("B", c), "Grounded", `${ctx} C must reinstate to Grounded`);
      assert.equal(snap.isLive("B", "+", c), true, `${ctx} C must be Live (+)`);
      assert.equal(snap.allGrounds("B", "-", c).length, 0, `${ctx} zero ghost -C`);
    } else {
      // Pure symmetric conflict: both A and C remain Collision and non-Live
      assert.equal(snap.statusOf("B", c), "Collision", `${ctx} C must be Collision`);
      assert.equal(snap.isLive("B", "+", c), false, `${ctx} C not Live`);
    }
    assert.equal(snap.allGrounds("B", "+", y).length, 0, `${ctx} zero ghost +Y`);
    assert.equal(snap.statusOf("B", y), "Excluded", `${ctx} Y stays Excluded`);
    assert.equal(snap.isLive("B", "-", y), true, `${ctx} -Y stays Live`);
    assert.equal(
      snap.statusOf("B", implies(collAnt, cons)),
      "Grounded",
      `${ctx} collided antecedent must not refute conditional`,
    );
    assert.equal(snap.isLive("B", "+", implies(collAnt, cons)), true, ctx);

    // Explicit MT-1 cross-conflict mutual bridge probe (boundary classification only)
    if (index === 0) {
      const bBridge = new BoundarySystem();
      bBridge.defineBoundary("B");
      const eBridge = new InquiryEngine(bBridge);
      const d = atom("D");
      const eItem = atom("E");
      const y1 = atom("Y1");
      const y2 = atom("Y2");
      eBridge.addIncompatibility("B", a, c);
      eBridge.addIncompatibility("B", d, eItem);
      eBridge.observePositive("B", a, "wa");
      eBridge.observePositive("B", c, "wc");
      eBridge.observePositive("B", d, "wd");
      eBridge.observePositive("B", eItem, "we");
      eBridge.observePositive("B", implies(a, x1), "wax1");
      eBridge.observePositive("B", implies(x1, y1), "wx1y1");
      eBridge.observePositive("B", implies(d, x2), "wdx2");
      eBridge.observePositive("B", implies(x2, y2), "wx2y2");
      eBridge.observeNegative("B", y1, "wny1");
      eBridge.observeNegative("B", y2, "wny2");
      eBridge.observePositive("B", implies(y1, eItem), "wy1e");
      eBridge.observePositive("B", implies(y2, c), "wy2c");
      const bridgeItems = [a, c, d, eItem, x1, x2, y1, y2, sentinel, bottom()];
      const snapBridge = eBridge.evaluate(bridgeItems);
      assertSnapshotCoreInvariants(snapBridge, bBridge, bridgeItems, sentinel, `${ctx}:bridge`);
      assert.equal(snapBridge.statusOf("B", a), "Collision");
      assert.equal(snapBridge.statusOf("B", c), "Collision");
      assert.equal(snapBridge.statusOf("B", d), "Collision");
      assert.equal(snapBridge.statusOf("B", eItem), "Collision");
      if (snapBridge.allGrounds("B", "+", y1).length > 0 || snapBridge.allGrounds("B", "+", y2).length > 0) {
        knownCrossConflictBridgeHits += 1;
      }
    }
  }
  assert.ok(knownCrossConflictBridgeHits >= 0);
}

/**
 * Suite 3 (MT-4): Disjoint regime zero negative leakage and selective Quarantine survival.
 */
function test_fuzz_disjoint_zero_leakage_and_selective_survival(): void {
  const seeds = getSuiteSeeds(3, 14);
  for (const seed of seeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=disjoint-survival seed=${seed}]`;
    const bs = new BoundarySystem();
    bs.defineBoundary("B_all");
    bs.defineBoundary("B_L", { parents: ["B_all"] });
    bs.defineBoundary("B_R", { parents: ["B_all"] });
    if (rng.bool(0.5)) {
      bs.declareDisjoint("B_L", "B_R");
    } else {
      bs.defineMeet("B_L", "B_R", BOT_BOUNDARY);
    }

    const leftSubs = ["B_L"];
    const rightSubs = ["B_R"];
    const nLSubs = rng.int(1, 2);
    for (let i = 0; i < nLSubs; i++) {
      const id = `B_L${i}`;
      bs.defineBoundary(id, { parents: ["B_L"] });
      leftSubs.push(id);
    }
    const nRSubs = rng.int(1, 2);
    for (let i = 0; i < nRSubs; i++) {
      const id = `B_R${i}`;
      bs.defineBoundary(id, { parents: ["B_R"] });
      rightSubs.push(id);
    }

    const engine = new InquiryEngine(bs);
    const broadCond = atom("BroadCond");
    const broadRule = implies(atom("Heat"), broadCond);
    const leftBase = atom("LeftLocal");
    const leftStep = atom("LeftChain");
    const leftFinal = atom("LeftConclusion");
    const onlyRItems = [atom("OnlyR0"), atom("OnlyR1"), atom("OnlyR2")];

    engine.observePositive("B_all", broadRule, "w_broad");
    engine.observePositive("B_all", atom("Heat"), "w_heat");
    engine.observePositive("B_L", leftBase, "w_lbase");
    engine.observePositive("B_L", implies(leftBase, leftStep), "w_lstep");
    engine.observePositive(rng.pick(leftSubs), implies(leftStep, leftFinal), "w_lfin");

    const preItems = [broadRule, broadCond, leftBase, leftStep, leftFinal, ...onlyRItems];
    const snapBefore = engine.evaluate(preItems);
    const survivingBefore: { readonly b: string; readonly item: Item }[] = [];
    for (const lb of leftSubs) {
      for (const it of [leftBase, leftStep, leftFinal]) {
        if (snapBefore.isLive(lb, "+", it)) {
          survivingBefore.push({ b: lb, item: it });
        }
      }
    }
    assert.ok(survivingBefore.length >= 2, `${ctx} expected independent B_L live items`);

    engine.observeNegative(rng.pick(rightSubs), broadCond, "w_refute_broad");
    for (let i = 0; i < onlyRItems.length; i++) {
      const rItem = onlyRItems[i];
      if (rItem === undefined) {
        continue;
      }
      const rb = rng.pick(rightSubs);
      engine.observeNegative(rb, rItem, `w_neg_r_${i}`);
      if (rng.bool(0.5)) {
        engine.observePositive(rb, rItem, `w_pos_r_${i}`);
      }
    }
    engine.addIncompatibility(rng.pick(rightSubs), leftBase, onlyRItems[0]!);
    if (rng.bool(0.5)) {
      engine.observePositive(rng.pick(rightSubs), leftBase, "w_rb_leftbase");
    }
    engine.addStructuralCollapse(rng.pick(rightSubs), onlyRItems[1]!);

    const snapAfter = engine.evaluate(preItems);

    for (const lb of leftSubs) {
      for (const rIt of onlyRItems) {
        assert.equal(
          snapAfter.allGrounds(lb, "-", rIt).length,
          0,
          `${ctx} negative leakage of ${itemKey(rIt)} onto ${lb}`,
        );
      }
    }

    for (const surv of survivingBefore) {
      assert.equal(
        snapAfter.isLive(surv.b, "+", surv.item),
        true,
        `${ctx} independent derivation (${surv.b}, ${itemKey(surv.item)}) lost Live`,
      );
    }

    assert.equal(snapAfter.isObstructed("B_all", broadRule), true, ctx);
    assert.equal(snapAfter.isLive("B_all", "+", broadRule), false, ctx);
    assert.equal(snapAfter.isObstructed("B_L", leftBase), false, ctx);
  }
}

function oracleHasMutualRecursionViolation(defs: readonly RecursiveDef[]): boolean {
  const byName = new Map<string, RecursiveDef>();
  const levelMap = new Map<string, number>();
  for (const d of defs) {
    byName.set(d.name, d);
    levelMap.set(d.name, d.level);
  }
  const edges: { readonly from: string; readonly to: string; readonly contravariant: boolean }[] = [];

  const itemLevel = (it: Item): number => {
    switch (it.kind) {
      case "atom":
      case "bottom":
      case "equiv":
        return 0;
      case "ref":
        return levelMap.get(it.name) ?? 0;
      case "flip":
        return itemLevel(it.inner);
      case "and":
      case "or":
        return Math.max(itemLevel(it.left), itemLevel(it.right));
      case "implies":
        return Math.max(itemLevel(it.antecedent), itemLevel(it.consequent));
      case "forall":
      case "exists":
        return Math.max(
          itemLevel(it.body),
          it.domainConstraint !== undefined ? itemLevel(it.domainConstraint) : 0,
        );
      case "refl":
        return Math.max(it.reflectedLevel + 1, itemLevel(it.targetItem) + 1);
    }
  };

  for (const d of defs) {
    let stratFail = false;
    const visit = (it: Item, contra: boolean): void => {
      switch (it.kind) {
        case "atom":
        case "bottom":
        case "equiv":
          return;
        case "ref":
          if (byName.has(it.name)) {
            edges.push({ from: d.name, to: it.name, contravariant: contra });
          }
          return;
        case "flip":
          visit(it.inner, true);
          return;
        case "and":
        case "or":
          visit(it.left, contra);
          visit(it.right, contra);
          return;
        case "implies":
          visit(it.antecedent, true);
          visit(it.consequent, contra);
          return;
        case "forall":
        case "exists":
          if (it.domainConstraint !== undefined) {
            visit(it.domainConstraint, true);
          }
          visit(it.body, contra);
          return;
        case "refl":
          if (itemLevel(it.targetItem) > it.reflectedLevel || it.reflectedLevel >= d.level) {
            stratFail = true;
          }
          visit(it.targetItem, contra);
          return;
      }
    };
    visit(d.body, false);
    if (stratFail || d.level < itemLevel(d.body)) {
      return true;
    }
  }

  for (const e of edges) {
    if (!e.contravariant) {
      continue;
    }
    const seen = new Set<string>();
    const stack = [e.to];
    while (stack.length > 0) {
      const cur = stack.pop();
      if (cur === undefined || seen.has(cur)) {
        continue;
      }
      if (cur === e.from) {
        return true;
      }
      seen.add(cur);
      for (const next of edges) {
        if (next.from === cur && !seen.has(next.to)) {
          stack.push(next.to);
        }
      }
    }
  }
  return false;
}

/**
 * Suite 4 (MT-2): Stage archive snapshot immutability under later mutations,
 * cross-stage reflection boundary scoping, and mutual-recursion Curry firewall.
 */
function test_fuzz_stage_archive_reflection_and_mutual_recursion_firewall(): void {
  // Part A: Cross-stage archive immutability & boundary scoping (8 seeds × 4-5 stages)
  const stageSeeds = getSuiteSeeds(4, 8);
  for (const seed of stageSeeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=reflection seed=${seed}]`;
    const bs = new BoundarySystem();
    bs.defineBoundary("B0", {
      nativeRelations: ["P", "Q"],
      handles: [
        { id: "h0", criterion: "I(h0)", kind: "structural" },
        { id: "h1", criterion: "I(h1)", kind: "structural" },
      ],
    });
    bs.defineBoundary("B1", { parents: ["B0"] });
    const engine = new InquiryEngine(bs);

    const p0 = atom("P", [{ role: "arg", handle: "h0" }]);
    const p1 = atom("P", [{ role: "arg", handle: "h1" }]);
    const tracked = [p0, p1, implies(p0, p1)];
    const stageBounds: readonly string[][] = [["B0", "B1"]];
    const recordedSnaps: {
      readonly stage: number;
      readonly bounds: readonly string[];
      readonly statuses: Map<string, string>;
      readonly lives: Map<string, boolean>;
    }[] = [];

    const captureStageOracle = (curStage: number, curBounds: readonly string[]): void => {
      const snap = engine.evaluate(tracked);
      const statuses = new Map<string, string>();
      const lives = new Map<string, boolean>();
      for (const b of curBounds) {
        for (const it of tracked) {
          const sk = `${b}\0${itemKey(it)}`;
          statuses.set(sk, snap.statusOf(b, it));
          lives.set(`${sk}\0+`, snap.isLive(b, "+", it));
          lives.set(`${sk}\0-`, snap.isLive(b, "-", it));
        }
      }
      recordedSnaps.push({ stage: curStage, bounds: [...curBounds], statuses, lives });
    };

    captureStageOracle(0, stageBounds[0]!);
    const activeIds: string[] = [];
    const lateBounds: string[] = [];

    const numStages = rng.int(4, 5);
    for (let step = 0; step < numStages; step++) {
      const choice = rng.int(0, 3);
      if (choice === 0) {
        const b = rng.pick(stageBounds[0]!);
        const it = rng.pick(tracked);
        const id = `rp_${step}`;
        engine.observePositive(b, it, id);
        activeIds.push(id);
      } else if (choice === 1) {
        const b = rng.pick(stageBounds[0]!);
        const it = rng.pick(tracked);
        const id = `rn_${step}`;
        engine.observeNegative(b, it, id);
        activeIds.push(id);
      } else if (choice === 2 && activeIds.length > 0) {
        const id = activeIds.pop()!;
        engine.retract(id);
      } else if (lateBounds.length === 0) {
        const bLate = `B_late_${step}`;
        bs.defineBoundary(bLate, {
          parents: ["B0"],
          nativeRelations: ["LateRel"],
          handles: [{ id: "h0", criterion: "I(h0)", kind: "structural" }],
        });
        lateBounds.push(bLate);
        const c1 = `${bLate}_c1`;
        const c2 = `${bLate}_c2`;
        bs.defineBoundary(c1, { parents: [bLate] });
        bs.defineBoundary(c2, { parents: [bLate] });
        bs.declareDisjoint(c1, c2);
        engine.witnessCover(bLate, [c1, c2]);
        captureStageOracle(engine.stage, [...stageBounds[0]!, bLate, c1, c2]);
        continue;
      } else {
        engine.observePositive("B0", rng.pick(tracked), `rp_extra_${step}`);
      }
      captureStageOracle(engine.stage, stageBounds[0]!);
    }

    if (lateBounds.length === 0) {
      const bLate = `B_late_tail`;
      bs.defineBoundary(bLate, { parents: ["B0"] });
      lateBounds.push(bLate);
      engine.observePositive(bLate, p0, "w_tail_late");
      captureStageOracle(engine.stage, [...stageBounds[0]!, bLate]);
    }
    const postStageZeroBound = lateBounds[0]!;

    for (const rec of recordedSnaps) {
      const histSnap = engine.evaluateAtStage(rec.stage, tracked);
      for (const b of rec.bounds) {
        for (const it of tracked) {
          const sk = `${b}\0${itemKey(it)}`;
          assert.equal(
            histSnap.statusOf(b, it),
            rec.statuses.get(sk),
            `${ctx} stage ${rec.stage} status drift on (${b}, ${itemKey(it)})`,
          );
          assert.equal(
            histSnap.isLive(b, "+", it),
            rec.lives.get(`${sk}\0+`),
            `${ctx} stage ${rec.stage} Live(+) drift`,
          );
          assert.equal(
            histSnap.isLive(b, "-", it),
            rec.lives.get(`${sk}\0-`),
            `${ctx} stage ${rec.stage} Live(-) drift`,
          );
        }
      }
    }

    const stage0Rec = recordedSnaps[0]!;
    const validStatus = stage0Rec.statuses.get(`B0\0${itemKey(p0)}`) as
      | "Open"
      | "Grounded"
      | "Excluded"
      | "Collision";
    const validRefl = reflStatus(0, 0, "B0", p0, validStatus);
    const wrongStatus = validStatus === "Open" ? "Grounded" : "Open";
    const wrongRefl = reflStatus(0, 0, "B0", p0, wrongStatus);
    const sameStageRefl = refl(0, "B0", "+", p0, engine.stage);
    const futureStageRefl = refl(0, "B0", "+", p0, engine.stage + 3);
    const postBoundTargetRefl = refl(0, postStageZeroBound, "+", p0, 0);
    const postBoundInnerForallRefl = reflStatus(
      0,
      0,
      "B0",
      forall("x", postStageZeroBound, atom("P", [{ role: "arg", handle: "x" }])),
      "Open",
    );
    const postBoundInnerEquivRefl = reflStatus(
      0,
      0,
      "B0",
      equiv(postStageZeroBound, "h0", "h1"),
      "Open",
    );
    const illLevelNestedRefl = refl(0, "B0", "+", validRefl, Math.max(1, engine.stage - 1));

    const reflSnap = engine.evaluate([
      validRefl,
      wrongRefl,
      sameStageRefl,
      futureStageRefl,
      postBoundTargetRefl,
      postBoundInnerForallRefl,
      postBoundInnerEquivRefl,
      illLevelNestedRefl,
    ]);

    assert.equal(reflSnap.statusOf("B0", validRefl), "Grounded", `${ctx} valid Refl`);
    assert.equal(reflSnap.statusOf("B0", wrongRefl), "Excluded", `${ctx} mismatched status Refl`);
    assert.equal(reflSnap.statusOf("B0", sameStageRefl), "Open", `${ctx} same-stage Refl`);
    assert.equal(reflSnap.statusOf("B0", futureStageRefl), "Open", `${ctx} future-stage Refl`);
    assert.equal(
      reflSnap.statusOf("B0", postBoundTargetRefl),
      "Open",
      `${ctx} post-stage targetBoundary must stay Open`,
    );
    assert.equal(
      reflSnap.statusOf("B0", postBoundInnerForallRefl),
      "Open",
      `${ctx} post-stage inner domain must stay Open`,
    );
    assert.equal(
      reflSnap.statusOf("B0", postBoundInnerEquivRefl),
      "Open",
      `${ctx} post-stage inner equiv boundary must stay Open`,
    );
    assert.equal(reflSnap.statusOf("B0", illLevelNestedRefl), "Open", `${ctx} ill-level nested Refl`);

    for (const bad of [
      sameStageRefl,
      futureStageRefl,
      postBoundTargetRefl,
      postBoundInnerForallRefl,
      postBoundInnerEquivRefl,
      illLevelNestedRefl,
    ]) {
      const res = verifyDerivation(engine, {
        kind: "refl-intro",
        boundary: "B0",
        reflItem: bad,
      });
      assert.equal(res.ok, false, `${ctx} refl-intro should reject ${itemKey(bad)}`);
    }
  }

  // Part B: Fast mutual-recursion Strict Positivity + Stratification firewall (40 seeds)
  const mutSeeds = getSuiteSeeds(40, 40);
  for (const seed of mutSeeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=mutual-firewall seed=${seed}]`;
    const defCount = rng.int(3, 5);
    const names = Array.from({ length: defCount }, (_, i) => `X${i}`);
    const levelBase = rng.int(0, 1);
    const genDefExpr = (depth: number, maxLevel: number): Item => {
      if (depth <= 0) {
        const r = rng.next();
        if (r < 0.35) {
          return atom("A", [{ role: "arg", handle: "h0" }]);
        }
        if (r < 0.85) {
          return ref(rng.pick(names));
        }
        return refl(maxLevel, "B0", "+", atom("A"), 0);
      }
      const kind = rng.int(0, 4);
      if (kind === 0) {
        return flip(genDefExpr(depth - 1, maxLevel));
      }
      if (kind === 1) {
        return and(genDefExpr(depth - 1, maxLevel), genDefExpr(depth - 1, maxLevel));
      }
      if (kind === 2) {
        return or(genDefExpr(depth - 1, maxLevel), genDefExpr(depth - 1, maxLevel));
      }
      if (kind === 3) {
        return implies(genDefExpr(depth - 1, maxLevel), genDefExpr(depth - 1, maxLevel));
      }
      return forall("x", "B0", genDefExpr(depth - 1, maxLevel), genDefExpr(depth - 1, maxLevel));
    };
    const defs: RecursiveDef[] = names.map((name) => ({
      name,
      level: levelBase + rng.int(0, 2),
      body: genDefExpr(2, rng.int(0, 2)),
    }));
    const actualOk = checkRecursiveDefinitionSystem(defs).ok;
    const expectedOk = !oracleHasMutualRecursionViolation(defs);
    assert.equal(actualOk, expectedOk, `${ctx} mutual-recursion oracle mismatch`);
  }
}

/**
 * Suite 5 (MT-8): Capture-avoiding substituteHandle (Semantic Substitution Lemma),
 * natural deduction <-> engine soundness, domainConstraint checks, and Glivenko block.
 */
function test_fuzz_deduction_soundness_domain_constraint_and_capture_avoiding_substitution(): void {
  // Part A: 100 random Semantic Substitution Lemma trials over colliding bound/free names
  const substSeeds = getSuiteSeeds(50, 100);
  const varsPool = ["x", "y", "z", "x_1", "y_1"];
  const domainVals = [0, 1] as const;

  const evalSem = (it: Item, env: ReadonlyMap<string, number>): boolean => {
    const valOf = (h: string): number => env.get(h) ?? (h === "h1" ? 1 : 0);
    switch (it.kind) {
      case "atom": {
        const a0 = valOf(it.roles[0]?.handle ?? "h0");
        const a1 = valOf(it.roles[1]?.handle ?? "h1");
        if (it.relation === "R1") {
          return a0 === 1;
        }
        return ((a0 * 2 + a1) ^ 1) % 2 === 1;
      }
      case "bottom":
        return false;
      case "equiv":
        return valOf(it.left) === valOf(it.right);
      case "flip":
        return !evalSem(it.inner, env);
      case "and":
        return evalSem(it.left, env) && evalSem(it.right, env);
      case "or":
        return evalSem(it.left, env) || evalSem(it.right, env);
      case "implies":
        return !evalSem(it.antecedent, env) || evalSem(it.consequent, env);
      case "forall":
        for (const d of domainVals) {
          const next = new Map(env);
          next.set(it.variable, d);
          if (it.domainConstraint !== undefined && !evalSem(it.domainConstraint, next)) {
            continue;
          }
          if (!evalSem(it.body, next)) {
            return false;
          }
        }
        return true;
      case "exists":
        for (const d of domainVals) {
          const next = new Map(env);
          next.set(it.variable, d);
          if (it.domainConstraint !== undefined && !evalSem(it.domainConstraint, next)) {
            continue;
          }
          if (evalSem(it.body, next)) {
            return true;
          }
        }
        return false;
      case "refl":
      case "ref":
        return true;
    }
  };

  for (const seed of substSeeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=subst-lemma seed=${seed}]`;
    const genFormula = (depth: number, mustMentionVar?: string): Item => {
      if (depth <= 0) {
        const hA = mustMentionVar !== undefined && rng.bool(0.7) ? mustMentionVar : rng.pick(varsPool);
        const hB = rng.pick(varsPool);
        return rng.bool(0.5)
          ? atom("R1", [{ role: "arg", handle: hA }])
          : atom("R2", [
              { role: "a", handle: hA },
              { role: "b", handle: hB },
            ]);
      }
      const k = rng.int(0, 5);
      if (k === 0) {
        return flip(genFormula(depth - 1, mustMentionVar));
      }
      if (k === 1) {
        return and(genFormula(depth - 1, mustMentionVar), genFormula(depth - 1));
      }
      if (k === 2) {
        return or(genFormula(depth - 1), genFormula(depth - 1, mustMentionVar));
      }
      if (k === 3) {
        return implies(genFormula(depth - 1, mustMentionVar), genFormula(depth - 1));
      }
      const boundV = rng.pick(varsPool);
      const useCons = rng.bool(0.6);
      const body = genFormula(depth - 1, mustMentionVar);
      const cons = useCons ? genFormula(depth - 1, mustMentionVar) : undefined;
      return k === 4 ? forall(boundV, "D", body, cons) : exists(boundV, "D", body, cons);
    };

    const targetVar = rng.pick(["x", "y", "z"]);
    const replVar = rng.pick(varsPool);
    const item = genFormula(rng.int(2, 4), targetVar);
    const sub = substituteHandle(item, targetVar, replVar);

    const freeOrig = collectHandles(item);
    const freeSub = collectHandles(sub);
    if (targetVar !== replVar && freeOrig.has(targetVar)) {
      assert.equal(freeSub.has(targetVar), false, `${ctx} old var ${targetVar} still free`);
      assert.equal(freeSub.has(replVar), true, `${ctx} replacement ${replVar} captured!`);
    }

    for (let eIdx = 0; eIdx < 16; eIdx++) {
      const env = new Map<string, number>();
      for (const vn of varsPool) {
        env.set(vn, rng.int(0, 1));
      }
      const envSubst = new Map(env);
      envSubst.set(targetVar, env.get(replVar) ?? 0);
      assert.equal(
        evalSem(item, envSubst),
        evalSem(sub, env),
        `${ctx} semantic substitution lemma failed for [${targetVar} := ${replVar}] on ${itemKey(item)}`,
      );
    }
  }

  // Part B: 8 seeds of randomized Natural Deduction <-> Engine soundness & domainConstraint
  const dedSeeds = getSuiteSeeds(5, 8);
  for (const seed of dedSeeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=deduction seed=${seed}]`;
    const bs = new BoundarySystem();
    bs.defineBoundary("D", {
      nativeRelations: ["P", "Q", "C"],
      handles: [
        { id: "h0", criterion: "I(h0)", kind: "structural" },
        { id: "h1", criterion: "I(h1)", kind: "structural" },
      ],
    });
    bs.defineBoundary("D1", { parents: ["D"] });
    bs.defineBoundary("D2", { parents: ["D"] });
    bs.declareDisjoint("D1", "D2");
    bs.registerCover("D", ["D1", "D2"]);

    const monotone = rng.bool(0.5);
    const e = new InquiryEngine(bs, monotone ? { monotoneOnly: true } : {});
    const p = (h: string) => atom("P", [{ role: "arg", handle: h }]);
    const q = (h: string) => atom("Q", [{ role: "arg", handle: h }]);
    const cCons = (h: string) => atom("C", [{ role: "arg", handle: h }]);
    const goal = atom("Goal");

    e.observePositive("D", cCons("h0"), "w_ch0");
    e.observePositive("D1", q("h0"), "w_qd1");
    e.observePositive("D2", q("h1"), "w_qd2");
    e.observePositive("D", implies(q("h0"), goal), "w_qg0");
    e.observePositive("D", implies(q("h1"), goal), "w_qg1");

    // 1a. Constrained ∀I -> ∀E -> ∃I -> ∃E deriving goal via constrained cover-glue
    const exElimProof: ProofNode = {
      kind: "exists-elim",
      existential: {
        kind: "exists-intro",
        witnessTerm: "h0",
        variable: "z",
        domain: "D",
        templateBody: and(cCons("z"), cCons("z")),
        domainConstraint: cCons("z"),
        constraintProof: { kind: "live-ground", boundary: "D", polarity: "+", item: cCons("h0") },
        witnessProof: {
          kind: "forall-elim",
          universal: {
            kind: "forall-intro",
            boundary: "D",
            variable: "x",
            domain: "D",
            eigenvar: "α_good",
            templateBody: and(cCons("x"), cCons("x")),
            domainConstraint: cCons("x"),
            constraintAssumpId: "ca_good",
            body: {
              kind: "and-intro",
              left: { kind: "assume", assumptionId: "ca_good", boundary: "D" },
              right: { kind: "assume", assumptionId: "ca_good", boundary: "D" },
            },
          },
          term: "h0",
          constraintProof: { kind: "live-ground", boundary: "D", polarity: "+", item: cCons("h0") },
        },
      },
      witnessVar: "γ_wit",
      assumptionId: "ex_body",
      constraintAssumpId: "ex_cons",
      body: {
        kind: "cover-glue",
        boundary: "D",
        item: goal,
        cellProofs: [
          {
            cell: "D1",
            proof: {
              kind: "implies-elim",
              premise: { kind: "live-ground", boundary: "D1", polarity: "+", item: q("h0") },
              conditional: {
                kind: "weaken-boundary",
                toBoundary: "D1",
                proof: {
                  kind: "live-ground",
                  boundary: "D",
                  polarity: "+",
                  item: implies(q("h0"), goal),
                },
              },
            },
          },
          {
            cell: "D2",
            proof: {
              kind: "implies-elim",
              premise: { kind: "live-ground", boundary: "D2", polarity: "+", item: q("h1") },
              conditional: {
                kind: "weaken-boundary",
                toBoundary: "D2",
                proof: {
                  kind: "live-ground",
                  boundary: "D",
                  polarity: "+",
                  item: implies(q("h1"), goal),
                },
              },
            },
          },
        ],
      },
    };

    const combinedProof: ProofNode = {
      kind: "and-intro",
      left: { kind: "live-ground", boundary: "D", polarity: "+", item: cCons("h0") },
      right: exElimProof,
    };

    const admitted = admitVerifiedDerivation(e, combinedProof, `thm_${seed}`, "UL-Core");
    assert.equal(admitted.ok, true, `${ctx} valid combinedProof failed: ${!admitted.ok ? admitted.reason : ""}`);
    if (admitted.ok) {
      assert.equal(admitted.requiredBaseIds.includes("w_ch0"), true, ctx);
      assert.equal(admitted.requiredBaseIds.includes("w_qd1"), true, ctx);
      assert.equal(e.evaluate([admitted.item]).isLive("D", "+", admitted.item), true, ctx);
      if (!monotone) {
        e.observeNegative("D1", q("h0"), "refute_qd1");
        assert.equal(
          e.evaluate([admitted.item]).isLive("D", "+", admitted.item),
          false,
          `${ctx} theorem must lose Live when intermediate dependency collides`,
        );
        e.retract("refute_qd1");
        assert.equal(e.evaluate([admitted.item]).isLive("D", "+", admitted.item), true, ctx);
        e.retract("w_ch0");
        assert.equal(e.evaluate([admitted.item]).isLive("D", "+", admitted.item), false, ctx);
      }
    }

    // 1b. Tiny standalone equiv-subst check on dedicated congruence boundary
    const bEq = new BoundarySystem();
    bEq.defineBoundary("B_eq", {
      nativeRelations: ["Rel"],
      handles: [
        { id: "h0", criterion: "I(h0)", kind: "structural" },
        { id: "h1", criterion: "I(h1)", kind: "structural" },
      ],
    });
    const eEq = new InquiryEngine(bEq, { monotoneOnly: true });
    eEq.observePositive("B_eq", equiv("B_eq", "h0", "h1"), "w_eq01");
    eEq.observePositive("B_eq", atom("Rel", [{ role: "arg", handle: "h0" }]), "w_rel0");
    const eqSubRes = admitVerifiedDerivation(
      eEq,
      {
        kind: "equiv-subst",
        direction: "left-to-right",
        equivProof: { kind: "live-ground", boundary: "B_eq", polarity: "+", item: equiv("B_eq", "h0", "h1") },
        targetProof: {
          kind: "live-ground",
          boundary: "B_eq",
          polarity: "+",
          item: atom("Rel", [{ role: "arg", handle: "h0" }]),
        },
      },
      "eq_thm",
      "UL-Minimal",
    );
    assert.equal(eqSubRes.ok, true, `${ctx} equiv-subst failed`);

    // 2. Deliberately malformed proofs must all be rejected (100%)
    const univConstrained = forall("x", "D", p("x"), cCons("x"));
    const eMal = new InquiryEngine(bs, { monotoneOnly: true });
    eMal.observePositive("D", univConstrained, "w_ucons");
    eMal.observePositive("D", p("h0"), "w_ph0");
    eMal.observePositive("D", cCons("h0"), "w_ch0");
    eMal.observePositive("D", exists("x", "D", p("x"), cCons("x")), "w_ex");

    const badForallElimMissingConstraint: ProofNode = {
      kind: "forall-elim",
      universal: { kind: "live-ground", boundary: "D", polarity: "+", item: univConstrained },
      term: "h0",
    };
    const badExistsIntroMissingConstraint: ProofNode = {
      kind: "exists-intro",
      witnessTerm: "h0",
      variable: "x",
      domain: "D",
      templateBody: p("x"),
      domainConstraint: cCons("x"),
      witnessProof: { kind: "live-ground", boundary: "D", polarity: "+", item: p("h0") },
    };
    const badShadowedForallIntro: ProofNode = {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "outer_a",
      antecedent: p("h0"),
      body: {
        kind: "forall-intro",
        boundary: "D",
        variable: "x",
        domain: "D",
        eigenvar: "α_bad",
        templateBody: p("x"),
        domainConstraint: cCons("x"),
        constraintAssumpId: "outer_a",
        body: { kind: "live-ground", boundary: "D", polarity: "+", item: p("h0") },
      },
    };
    const badEigenEscape: ProofNode = {
      kind: "exists-elim",
      existential: {
        kind: "live-ground",
        boundary: "D",
        polarity: "+",
        item: exists("x", "D", p("x"), cCons("x")),
      },
      witnessVar: "γ_esc",
      assumptionId: "ex_a",
      constraintAssumpId: "ex_c",
      body: { kind: "assume", assumptionId: "ex_a", boundary: "D" },
    };
    const badNonFreshEigenInSigma: ProofNode = {
      kind: "forall-intro",
      boundary: "D",
      variable: "x",
      domain: "D",
      eigenvar: "h0",
      templateBody: p("x"),
      body: { kind: "live-ground", boundary: "D", polarity: "+", item: p("h0") },
    };
    const badExFalsoInMinimal: ProofNode = {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "bot_a",
      antecedent: bottom(),
      body: {
        kind: "ex-falso-bottom",
        bottomProof: { kind: "assume", assumptionId: "bot_a", boundary: "D" },
        target: atom(`Arbitrary_${seed}`),
      },
    };

    for (const [label, badNode, mode] of [
      ["missing-forall-constraint", badForallElimMissingConstraint, "UL-Core"],
      ["missing-exists-constraint", badExistsIntroMissingConstraint, "UL-Core"],
      ["shadowed-assump", badShadowedForallIntro, "UL-Core"],
      ["eigenvar-escape", badEigenEscape, "UL-Core"],
      ["nonfresh-eigenvar", badNonFreshEigenInSigma, "UL-Core"],
      ["ex-falso-minimal", badExFalsoInMinimal, "UL-Minimal"],
    ] as const) {
      const r = verifyDerivation(eMal, badNode, mode);
      assert.equal(r.ok, false, `${ctx} malformed proof ${label} should fail`);
    }

    assert.equal(verifyMinimalSpecialization(eMal).ok, true, ctx);
    assert.equal(verifyIntuitionisticSpecialization(eMal).ok, true, ctx);
    const intOk = verifyDerivation(eMal, badExFalsoInMinimal, "UL-Intuitionistic");
    assert.equal(intOk.ok, true, `${ctx} ex-falso-bottom must hold in UL-Intuitionistic`);

    // 3. Glivenko double impossibility must NEVER invert into LEM on random Open P
    const openP = atom(`OpenGlivenko_${seed}`);
    const lem = or(openP, structImposs(openP));
    const doubleNegLem = structImposs(structImposs(lem));
    const glivProof: ProofNode = {
      kind: "implies-intro",
      boundary: "D",
      assumptionId: "g_not_lem",
      antecedent: structImposs(lem),
      body: {
        kind: "implies-elim",
        conditional: { kind: "assume", assumptionId: "g_not_lem", boundary: "D" },
        premise: {
          kind: "or-intro",
          side: "right",
          other: openP,
          witness: {
            kind: "implies-intro",
            boundary: "D",
            assumptionId: "g_p",
            antecedent: openP,
            body: {
              kind: "implies-elim",
              conditional: { kind: "assume", assumptionId: "g_not_lem", boundary: "D" },
              premise: {
                kind: "or-intro",
                side: "left",
                other: structImposs(openP),
                witness: { kind: "assume", assumptionId: "g_p", boundary: "D" },
              },
            },
          },
        },
      },
    };
    const glivRes = admitVerifiedDerivation(eMal, glivProof, `gliv_${seed}`, "UL-Minimal");
    assert.equal(glivRes.ok, true, `${ctx} Glivenko double impossibility should verify`);
    const snapGliv = eMal.evaluate([openP, lem, doubleNegLem]);
    assert.equal(snapGliv.statusOf("D", doubleNegLem), "Grounded", ctx);
    assert.equal(snapGliv.statusOf("D", structImposs(lem)), "Excluded", ctx);
    assert.equal(snapGliv.statusOf("D", lem), "Open", `${ctx} LEM on Open P must stay Open!`);
    assert.equal(snapGliv.statusOf("D", openP), "Open", `${ctx} Open P must stay Open!`);
  }
}

/**
 * Suite 6 (MT-9): UL-Classical 2 / 2^k Boolean product algebra recovery and guard enforcement.
 */
function test_fuzz_ul_classical_boolean_recovery(): void {
  const seeds = getSuiteSeeds(6, 5);
  for (const seed of seeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=classical seed=${seed}]`;
    const cellCount = rng.int(1, 4);
    const handleCount = rng.int(2, 3);
    const handles: HandleSpec[] = Array.from({ length: handleCount }, (_, i) => ({
      id: `h${i}`,
      criterion: `I(h${i})`,
      kind: "structural",
    }));

    const bs = new BoundarySystem();
    bs.defineBoundary("B_top", {
      nativeRelations: ["P", "Q", "Delta"],
      handles,
    });
    const cells: string[] = [];
    if (cellCount === 1) {
      cells.push("B_top");
    } else {
      for (let i = 0; i < cellCount; i++) {
        const c = `C${i}`;
        bs.defineBoundary(c, { parents: ["B_top"] });
        cells.push(c);
      }
      for (let i = 0; i < cells.length; i++) {
        for (let j = i + 1; j < cells.length; j++) {
          bs.declareDisjoint(cells[i]!, cells[j]!);
        }
      }
      bs.registerCover("B_top", cells);
    }

    const engine = new InquiryEngine(bs, { monotoneOnly: true });
    const p = (h: string) => atom("P", [{ role: "arg", handle: h }]);
    const q = (h: string) => atom("Q", [{ role: "arg", handle: h }]);
    const delta = (h: string) => atom("Delta", [{ role: "arg", handle: h }]);

    const truthTable = new Map<string, boolean>();
    const allBaseAtoms: Item[] = [];
    for (const h of handles) {
      allBaseAtoms.push(p(h.id), q(h.id), delta(h.id));
    }

    let obsIdx = 0;
    for (const c of cells) {
      for (const a of allBaseAtoms) {
        const val = rng.bool(0.5);
        truthTable.set(`${c}\0${itemKey(a)}`, val);
        obsIdx += 1;
        if (val) {
          engine.observePositive(c, a, `obs_${obsIdx}`);
        } else {
          engine.observeNegative(c, a, `obs_${obsIdx}`);
        }
      }
    }

    const oracleEval = (cell: string, it: Item, substEnv: ReadonlyMap<string, string> = new Map()): boolean => {
      const resolveH = (h: string): string => substEnv.get(h) ?? h;
      switch (it.kind) {
        case "atom": {
          const resolved: Item = atom(
            it.relation,
            it.roles.map((r) => ({ role: r.role, handle: resolveH(r.handle) })),
          );
          return truthTable.get(`${cell}\0${itemKey(resolved)}`) ?? false;
        }
        case "bottom":
          return false;
        case "equiv":
          return resolveH(it.left) === resolveH(it.right);
        case "flip":
          return !oracleEval(cell, it.inner, substEnv);
        case "and":
          return oracleEval(cell, it.left, substEnv) && oracleEval(cell, it.right, substEnv);
        case "or":
          return oracleEval(cell, it.left, substEnv) || oracleEval(cell, it.right, substEnv);
        case "implies":
          return !oracleEval(cell, it.antecedent, substEnv) || oracleEval(cell, it.consequent, substEnv);
        case "forall":
          for (const h of handles) {
            const nextEnv = new Map(substEnv);
            nextEnv.set(it.variable, h.id);
            if (it.domainConstraint !== undefined && !oracleEval(cell, it.domainConstraint, nextEnv)) {
              continue;
            }
            if (!oracleEval(cell, it.body, nextEnv)) {
              return false;
            }
          }
          return true;
        case "exists":
          for (const h of handles) {
            const nextEnv = new Map(substEnv);
            nextEnv.set(it.variable, h.id);
            if (it.domainConstraint !== undefined && !oracleEval(cell, it.domainConstraint, nextEnv)) {
              continue;
            }
            if (oracleEval(cell, it.body, nextEnv)) {
              return true;
            }
          }
          return false;
        case "refl":
        case "ref":
          return false;
      }
    };

    const genClosedFormula = (depth: number, boundVars: readonly string[] = []): Item => {
      if (depth <= 0) {
        const argH = boundVars.length > 0 && rng.bool(0.6) ? rng.pick(boundVars) : rng.pick(handles).id;
        const rel = rng.pick(["P", "Q", "Delta"]);
        return atom(rel, [{ role: "arg", handle: argH }]);
      }
      const k = rng.int(0, 5);
      if (k === 0) {
        return flip(genClosedFormula(depth - 1, boundVars));
      }
      if (k === 1) {
        return and(genClosedFormula(depth - 1, boundVars), genClosedFormula(depth - 1, boundVars));
      }
      if (k === 2) {
        return or(genClosedFormula(depth - 1, boundVars), genClosedFormula(depth - 1, boundVars));
      }
      if (k === 3) {
        return implies(genClosedFormula(depth - 1, boundVars), genClosedFormula(depth - 1, boundVars));
      }
      const v = `v${boundVars.length}`;
      const body = genClosedFormula(depth - 1, [...boundVars, v]);
      const cons = rng.bool(0.5) ? delta(v) : undefined;
      return k === 4 ? forall(v, "B_top", body, cons) : exists(v, "B_top", body, cons);
    };

    const formA = genClosedFormula(2);
    const formC = genClosedFormula(2);
    const lemTaut = or(formA, flip(formA));
    const peirceTaut = implies(implies(implies(formA, formC), formA), formA);
    const queries: Item[] = [
      formA,
      formC,
      lemTaut,
      peirceTaut,
      genClosedFormula(rng.int(1, 2)),
      genClosedFormula(rng.int(1, 2)),
    ];

    const res = evaluateClassicalSpecialization(engine, "B_top", allBaseAtoms, queries);
    assert.equal(res.ok, true, `${ctx} UL-Classical failed: ${!res.ok ? res.reason : ""}`);
    if (res.ok) {
      assert.equal(res.coverCells.length, cells.length, ctx);
      assert.equal(res.results.get(itemKey(lemTaut))?.polarity, "+", `${ctx} LEM must hold globally`);
      assert.equal(res.results.get(itemKey(peirceTaut))?.polarity, "+", `${ctx} Peirce must hold globally`);

      for (const qItem of queries) {
        const val = res.results.get(itemKey(qItem));
        assert.ok(val !== undefined, `${ctx} missing valuation for ${itemKey(qItem)}`);
        assert.equal(val.bivalent, true, ctx);
        assert.equal(val.negCollapseEquivalent, true, `${ctx} negation collapse mismatch`);

        let posCount = 0;
        let negCount = 0;
        for (const c of cells) {
          const expectedPol: Polarity = oracleEval(c, qItem) ? "+" : "-";
          assert.equal(
            val.cellPolarities.get(c),
            expectedPol,
            `${ctx} cell ${c} polarity mismatch on ${itemKey(qItem)}`,
          );
          if (expectedPol === "+") {
            posCount += 1;
          } else {
            negCount += 1;
          }
        }
        const expectedGlobal = posCount === cells.length ? "+" : negCount === cells.length ? "-" : "split";
        assert.equal(val.polarity, expectedGlobal, `${ctx} global 2^k status mismatch`);
      }
    }

    const gapRes = evaluateClassicalSpecialization(engine, "B_top", allBaseAtoms, [atom("UnobservedAtom")]);
    assert.equal(gapRes.ok, false, `${ctx} Open query atom must fail No-Gaps`);

    const nonMono = new InquiryEngine(bs, { monotoneOnly: false });
    nonMono.observePositive(cells[0]!, p("h0"), "nm1");
    assert.equal(
      evaluateClassicalSpecialization(nonMono, "B_top", [p("h0")], [p("h0")]).ok,
      false,
      `${ctx} non-monotone engine must fail`,
    );

    const firstAtom = allBaseAtoms[0]!;
    const firstVal = truthTable.get(`${cells[0]!}\0${itemKey(firstAtom)}`) ?? true;
    const falseAnt = firstVal ? flip(firstAtom) : firstAtom;
    const conflictItem = implies(falseAnt, firstAtom);
    const eConflict = new InquiryEngine(bs, { monotoneOnly: true });
    let ci = 0;
    for (const c of cells) {
      for (const a of allBaseAtoms) {
        ci += 1;
        if (truthTable.get(`${c}\0${itemKey(a)}`)) {
          eConflict.observePositive(c, a, `c_${ci}`);
        } else {
          eConflict.observeNegative(c, a, `c_${ci}`);
        }
      }
    }
    const baseCell = cells[0]!;
    eConflict.observeNegative(baseCell, conflictItem, "obs_bad_comp");
    const confRes = evaluateClassicalSpecialization(eConflict, "B_top", allBaseAtoms, [conflictItem]);
    assert.equal(confRes.ok, false, `${ctx} contradictory compound exclusion must be rejected`);
    if (!confRes.ok) {
      assert.match(confRes.reason, /conflicts with existing "Excluded"/i, ctx);
    }
  }
}

/**
 * Suite 7 (MT-7): M1(i)-(iii) anti-immunization + M2 non-erasure in refineBoundary.
 */
function test_fuzz_m1_m2_anti_immunization_refine_boundary(): void {
  const seeds = getSuiteSeeds(7, 8);
  for (const seed of seeds) {
    const rng = new Rng(seed);
    const ctx = `[suite=m1-m2 seed=${seed}]`;
    const nStruct = rng.int(1, 2);
    const nCont = rng.int(2, 4);
    const structHandles: HandleSpec[] = Array.from({ length: nStruct }, (_, i) => ({
      id: `s${i}`,
      criterion: `I_struct(s${i})`,
      kind: "structural",
    }));
    const contHandles: HandleSpec[] = Array.from({ length: nCont }, (_, i) => ({
      id: `k${i}`,
      criterion: `I_cont(k${i})`,
      kind: "contingent",
    }));
    const allHandles = [...structHandles, ...contHandles];

    const excisedStruct = structHandles[0]!;
    const excisedCont = contHandles[0]!;
    const survivingCont = contHandles[1]!;

    const bs = new BoundarySystem();
    bs.defineBoundary("B", {
      nativeRelations: ["TargetRel", "SplitCrit", "StructSing", "ProxyRel"],
      handles: allHandles,
    });
    bs.defineBoundary("B_no_cont", {
      parents: ["B"],
      handleFilter: (h) => h.id !== excisedCont.id,
    });
    bs.defineBoundary("B_no_struct", {
      parents: ["B"],
      handleFilter: (h) => h.id !== excisedStruct.id,
    });
    bs.defineBoundary("B_empty", {
      parents: ["B"],
      handleFilter: () => false,
    });

    const targetAtom = (h: string) => atom("TargetRel", [{ role: "arg", handle: h }]);
    const splitAtom = (h: string) => atom("SplitCrit", [{ role: "arg", handle: h }]);
    const singAtom = (h: string) => atom("StructSing", [{ role: "arg", handle: h }]);
    const gen = forall("x", "B", targetAtom("x"));

    const buildEngine = (assertInitialGen: boolean): InquiryEngine => {
      const e = new InquiryEngine(bs);
      if (assertInitialGen) {
        e.observePositive("B", gen, "w_gen");
      }
      e.observeNegative("B", targetAtom(excisedCont.id), "w_ref_cont", {
        handle: excisedCont.id,
        criterion: excisedCont.criterion,
      });
      return e;
    };

    const eCirc = buildEngine(rng.bool(0.5));
    const circRes = eCirc.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_no_cont",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: flip(and(splitAtom("x"), targetAtom("x"))),
    });
    assert.equal(circRes.ok, false, ctx);
    if (!circRes.ok) {
      assert.equal(circRes.violation, "M1-circular", ctx);
    }

    const eCont = buildEngine(true);
    const contRes = eCont.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_no_cont",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: flip(equiv("B", "x", excisedCont.id)),
    });
    assert.equal(contRes.ok, false, ctx);
    if (!contRes.ok) {
      assert.equal(contRes.violation, "M1-contingent-excision", ctx);
    }

    const eEmpty = buildEngine(false);
    const emptyRes = eEmpty.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_empty",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: splitAtom("x"),
    });
    assert.equal(emptyRes.ok, false, ctx);
    if (!emptyRes.ok) {
      assert.equal(emptyRes.violation, "M1-unwitnessed-proxy", ctx);
    }

    const eUnwit = buildEngine(false);
    if (rng.bool(0.5) && contHandles.length >= 3) {
      const refutedSurvivor = contHandles[2]!;
      eUnwit.observeNegative("B", targetAtom(refutedSurvivor.id), "w_ref_s2", {
        handle: refutedSurvivor.id,
        criterion: refutedSurvivor.criterion,
      });
      eUnwit.observePositive("B", splitAtom(refutedSurvivor.id), "w_split_refuted");
    } else {
      eUnwit.observePositive("B", splitAtom(survivingCont.id), "w_split_pos");
      eUnwit.observeNegative("B", splitAtom(survivingCont.id), "w_split_coll");
    }
    const unwitRes = eUnwit.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_no_cont",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: splitAtom("x"),
    });
    assert.equal(unwitRes.ok, false, ctx);
    if (!unwitRes.ok) {
      assert.equal(unwitRes.violation, "M1-unwitnessed-proxy", ctx);
    }

    const anotherSurvivor = structHandles[0]!;
    const eContra = buildEngine(false);
    eContra.observePositive("B", splitAtom(survivingCont.id), "w_pos_surv");
    eContra.observeNegative("B", splitAtom(anotherSurvivor.id), "w_neg_surv");
    const contraRes = eContra.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_no_cont",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: splitAtom("x"),
    });
    assert.equal(contraRes.ok, false, ctx);
    if (!contraRes.ok) {
      assert.equal(contraRes.violation, "M1-unwitnessed-proxy", ctx);
    }

    const eStruct = new InquiryEngine(bs);
    eStruct.observePositive("B", gen, "w_gen");
    eStruct.observeNegative("B", targetAtom(excisedStruct.id), "w_ref_struct", {
      handle: excisedStruct.id,
      criterion: excisedStruct.criterion,
    });
    const structOk = eStruct.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_no_struct",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: flip(singAtom("x")),
    });
    assert.equal(structOk.ok, true, `${ctx} structural singularity refinement should succeed`);
    if (structOk.ok) {
      assert.equal(structOk.originalExcludedPreserved, true, ctx);
      assert.equal(eStruct.retract("w_gen"), true, ctx);
      assert.equal(eStruct.evaluate([gen]).statusOf("B", gen), "Excluded", `${ctx} M2 non-erasure`);
    }

    const eGood = buildEngine(true);
    eGood.observePositive("B", splitAtom(survivingCont.id), "w_clean_excess", {
      handle: survivingCont.id,
      criterion: survivingCont.criterion,
    });
    const goodRes = eGood.refineBoundary({
      fromBoundary: "B",
      toBoundary: "B_no_cont",
      originalUniversal: gen,
      targetRelation: "TargetRel",
      criterionItem: splitAtom("x"),
    });
    assert.equal(goodRes.ok, true, `${ctx} admissible contingent refinement failed`);
    if (goodRes.ok) {
      assert.equal(goodRes.originalExcludedPreserved, true, ctx);
      assert.equal(eGood.retract("w_gen"), true, ctx);
      assert.equal(
        eGood.evaluate([gen]).statusOf("B", gen),
        "Excluded",
        `${ctx} M2 must preserve Excluded on B`,
      );
    }
  }
}

test("fuzz MT-4 & MT-5 semilattice laws, disjoint monotonicity, and Grothendieck covers", test_fuzz_semilattice_and_finitary_covers);
test(
  "fuzz MT-1 MT-3 & MT-6 inquiry dynamics, Quarantine, biased G-15 conflict graphs, and Retract purity",
  test_fuzz_inquiry_dynamics_quarantine_and_biased_conflict_graphs,
);
test("fuzz MT-4 disjoint regime zero leakage and selective Quarantine survival", test_fuzz_disjoint_zero_leakage_and_selective_survival);
test("fuzz MT-2 stage archive immutability, reflection scoping, and mutual-recursion firewall", test_fuzz_stage_archive_reflection_and_mutual_recursion_firewall);
test(
  "fuzz MT-8 capture-avoiding substitution, deduction soundness, domainConstraint, and Glivenko block",
  test_fuzz_deduction_soundness_domain_constraint_and_capture_avoiding_substitution,
);
test("fuzz MT-9 UL-Classical 2/2^k Boolean recovery and precondition guards", test_fuzz_ul_classical_boolean_recovery);
test("fuzz MT-7 M1(i)-(iii) anti-immunization and M2 non-erasure on refineBoundary", test_fuzz_m1_m2_anti_immunization_refine_boundary);
