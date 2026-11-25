/**
 * Boundary specializations (UL-Minimal, UL-Intuitionistic, UL-Classical)
 * derived purely via explicit closure conditions on (B, Σ).
 *
 * Implements spec/core.md §4 item 13 and spec/worked-examples.md §4.
 */

import { BOT_BOUNDARY } from "./boundary.ts";
import { EvaluationSnapshot, InquiryEngine } from "./engine.ts";
import { bottom, flip, itemKey, substituteHandle, type Item, type Polarity } from "./syntax.ts";

export type MinimalCheckResult =
  | { readonly ok: true; readonly snapshot: EvaluationSnapshot }
  | { readonly ok: false; readonly reason: string };

export type IntuitionisticCheckResult =
  | {
      readonly ok: true;
      readonly snapshot: EvaluationSnapshot;
      readonly exFalsoBottomVerified: boolean;
    }
  | { readonly ok: false; readonly reason: string };

export type GlobalCoverStatus = "+" | "-" | "split";

export type ClassicalValuation = {
  readonly bivalent: boolean;
  readonly polarity: GlobalCoverStatus;
  readonly cellPolarities: ReadonlyMap<string, Polarity>;
  readonly negCollapseEquivalent: boolean;
};

export type ClassicalEvaluationResult =
  | {
      readonly ok: true;
      readonly coverCells: readonly string[];
      readonly results: ReadonlyMap<string, ClassicalValuation>;
      readonly vacuousExplosionHolds: true;
    }
  | { readonly ok: false; readonly reason: string };

/** Verify UL-Minimal closure conditions: monotoneOnly + No-Gluts. */
export function verifyMinimalSpecialization(
  engine: InquiryEngine,
  queryItems: readonly Item[] = [],
): MinimalCheckResult {
  if (!engine.monotoneOnly) {
    return { ok: false, reason: "UL-Minimal requires monotoneOnly (Retract forbidden)." };
  }
  const snapshot = engine.evaluate(queryItems);
  if (!snapshot.isCollisionFree()) {
    return {
      ok: false,
      reason: `UL-Minimal requires No-Gluts; found ${snapshot.revisionObligations().length} collision(s).`,
    };
  }
  return { ok: true, snapshot };
}

/**
 * Verify UL-Intuitionistic closure conditions: UL-Minimal + boundary axiom ⊥ → C.
 * Confirms ⊥ has no positive witness on any non-empty boundary, keeping ⊥ → C sound under No-Gluts.
 */
export function verifyIntuitionisticSpecialization(
  engine: InquiryEngine,
  queryItems: readonly Item[] = [],
): IntuitionisticCheckResult {
  const min = verifyMinimalSpecialization(engine, queryItems);
  if (!min.ok) {
    return min;
  }
  const bot = bottom();
  for (const b of engine.boundaries.nonEmptyBoundaries()) {
    if (min.snapshot.allGrounds(b, "+", bot).length > 0) {
      return {
        ok: false,
        reason: `Soundness violation: non-empty boundary "${b}" has a witness for ⊥.`,
      };
    }
  }
  return {
    ok: true,
    snapshot: min.snapshot,
    exFalsoBottomVerified: true,
  };
}

/**
 * Evaluate items under UL-Classical closure conditions on `boundary`:
 * 1) Frozen Σ & No-Gluts;
 * 2) `boundary` is atomic or admits a witnessed finite cover `{B*_i}` of atomic cells;
 * 3) No-Gaps holds on every atom in every atomic cell `B*_i`.
 *
 * Returns classical bivalent valuations obtained strictly via No-Gaps closure on UL-Core's
 * dual-polarity rules (with zero conflicting rules added).
 */
export function evaluateClassicalSpecialization(
  engine: InquiryEngine,
  boundary: string,
  atoms: readonly Item[],
  queryItems: readonly Item[],
): ClassicalEvaluationResult {
  if (boundary === BOT_BOUNDARY) {
    return { ok: false, reason: `Cannot evaluate UL-Classical on "${BOT_BOUNDARY}".` };
  }
  if (!engine.monotoneOnly) {
    return { ok: false, reason: "UL-Classical requires a frozen/monotone Σ (monotoneOnly: true)." };
  }

  const groundAtomMap = new Map<string, Item>();
  const collectGroundAtoms = (item: Item): string | undefined => {
    switch (item.kind) {
      case "atom":
      case "equiv": {
        const k = itemKey(item);
        if (!groundAtomMap.has(k)) {
          groundAtomMap.set(k, item);
        }
        return undefined;
      }
      case "bottom":
        return undefined;
      case "flip":
        return collectGroundAtoms(item.inner);
      case "and":
      case "or":
        return collectGroundAtoms(item.left) ?? collectGroundAtoms(item.right);
      case "implies":
        return collectGroundAtoms(item.antecedent) ?? collectGroundAtoms(item.consequent);
      case "forall":
      case "exists": {
        for (const h of engine.boundaries.handlesOf(item.domain)) {
          const bodyErr = collectGroundAtoms(substituteHandle(item.body, item.variable, h.id));
          if (bodyErr !== undefined) {
            return bodyErr;
          }
          if (item.domainConstraint !== undefined) {
            const consErr = collectGroundAtoms(
              substituteHandle(item.domainConstraint, item.variable, h.id),
            );
            if (consErr !== undefined) {
              return consErr;
            }
          }
        }
        return undefined;
      }
      case "refl":
      case "ref":
        return `UL-Classical requires level n = 0 closed formulas; found "${item.kind}".`;
    }
  };

  for (const it of [...atoms, ...queryItems]) {
    const err = collectGroundAtoms(it);
    if (err !== undefined) {
      return { ok: false, reason: err };
    }
  }
  const allGroundAtoms = [...groundAtomMap.values()];

  const snap = engine.evaluate([...atoms, ...queryItems, ...allGroundAtoms]);
  if (!snap.isCollisionFree()) {
    return { ok: false, reason: "UL-Classical requires No-Gluts (zero collisions)." };
  }

  const atomicCover = engine.boundaries
    .witnessedCoversOf(boundary)
    .find((cover) => cover.length > 0 && cover.every((c) => engine.boundaries.isAtomic(c)));

  if (atomicCover === undefined) {
    return {
      ok: false,
      reason: `Boundary "${boundary}" is neither atomic nor covered by a witnessed finite atomic partition.`,
    };
  }

  // Enforce No-Gaps on all base atoms and congruences reachable across atoms and queryItems.
  for (const cell of atomicCover) {
    for (const a of allGroundAtoms) {
      const st = snap.statusOf(cell, a);
      if (st === "Open") {
        return {
          ok: false,
          reason: `No-Gaps violated in atomic cell "${cell}" for atom "${itemKey(a)}".`,
        };
      }
    }
  }

  let conflictReason: string | undefined;
  const evalOnAtomicCell = (cell: string, item: Item): Polarity => {
    const checkConsistent = (pol: Polarity): Polarity => {
      const st = snap.statusOf(cell, item);
      if ((st === "Grounded" && pol === "-") || (st === "Excluded" && pol === "+")) {
        conflictReason ??= `UL-Classical valuation of "${itemKey(item)}" (${pol}) conflicts with existing "${st}" ground on atomic cell "${cell}".`;
      }
      return pol;
    };

    switch (item.kind) {
      case "atom": {
        const st = snap.statusOf(cell, item);
        return checkConsistent(st === "Grounded" ? "+" : "-");
      }
      case "bottom":
        return checkConsistent("-");
      case "equiv": {
        const st = snap.statusOf(cell, item);
        return checkConsistent(st === "Grounded" ? "+" : "-");
      }
      case "flip":
        return checkConsistent(evalOnAtomicCell(cell, item.inner) === "+" ? "-" : "+");
      case "and":
        return checkConsistent(
          evalOnAtomicCell(cell, item.left) === "+" && evalOnAtomicCell(cell, item.right) === "+"
            ? "+"
            : "-",
        );
      case "or":
        return checkConsistent(
          evalOnAtomicCell(cell, item.left) === "+" || evalOnAtomicCell(cell, item.right) === "+"
            ? "+"
            : "-",
        );
      case "implies": {
        // Under atomic-generated No-Gaps + No-Gluts closure, non-refuted conditionals close to +.
        const ant = evalOnAtomicCell(cell, item.antecedent);
        const con = evalOnAtomicCell(cell, item.consequent);
        return checkConsistent(ant === "+" && con === "-" ? "-" : "+");
      }
      case "forall": {
        const handles = engine.boundaries.handlesOf(item.domain);
        for (const h of handles) {
          if (item.domainConstraint !== undefined) {
            const cInst = substituteHandle(item.domainConstraint, item.variable, h.id);
            if (evalOnAtomicCell(cell, cInst) === "-") {
              continue;
            }
          }
          const inst = substituteHandle(item.body, item.variable, h.id);
          if (evalOnAtomicCell(cell, inst) === "-") {
            return checkConsistent("-");
          }
        }
        return checkConsistent("+");
      }
      case "exists": {
        const handles = engine.boundaries.handlesOf(item.domain);
        for (const h of handles) {
          if (item.domainConstraint !== undefined) {
            const cInst = substituteHandle(item.domainConstraint, item.variable, h.id);
            if (evalOnAtomicCell(cell, cInst) === "-") {
              continue;
            }
          }
          const inst = substituteHandle(item.body, item.variable, h.id);
          if (evalOnAtomicCell(cell, inst) === "+") {
            return checkConsistent("+");
          }
        }
        return checkConsistent("-");
      }
      case "refl":
      case "ref":
        throw new Error(`UL-Classical requires level n = 0 closed formulas; found "${item.kind}".`);
    }
  };

  // On a k-cell cover {B*_i} ▷ B, UL-Classical recovers the product Boolean algebra 2^k:
  // distinguish uniformly "+" (globally grounded), uniformly "-" (globally excluded), and "split".
  const results = new Map<string, ClassicalValuation>();
  for (const q of queryItems) {
    const cellPolarities = new Map<string, Polarity>();
    for (const cell of atomicCover) {
      cellPolarities.set(cell, evalOnAtomicCell(cell, q));
    }
    if (conflictReason !== undefined) {
      return { ok: false, reason: conflictReason };
    }
    const values = [...cellPolarities.values()];
    const pol: GlobalCoverStatus = values.every((p) => p === "+")
      ? "+"
      : values.every((p) => p === "-")
        ? "-"
        : "split";
    // Verify negation collapse: ~q and (q → ⊥) have identical polarity on every atomic cell.
    const negCollapseEquivalent = atomicCover.every((cell) => {
      const pFlip = evalOnAtomicCell(cell, flip(q));
      const pImposs = evalOnAtomicCell(cell, { kind: "implies", antecedent: q, consequent: bottom() });
      return pFlip === pImposs;
    });
    results.set(itemKey(q), {
      bivalent: true,
      polarity: pol,
      cellPolarities,
      negCollapseEquivalent,
    });
  }

  return {
    ok: true,
    coverCells: atomicCover,
    results,
    vacuousExplosionHolds: true,
  };
}
