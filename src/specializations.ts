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
 * 2) `boundary` is atomic or admits a witnessed finite cover `{B*_i}` of atomic cells, and every
 *    quantifier domain D of the items is closed (CloseDomain), non-empty and within each Dom(B*_i) (C3);
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
  const quantifierDomains = new Set<string>();
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
        quantifierDomains.add(item.domain);
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

  // (C3): a witnessed atomic cover, hence valid (item 5), whose cells have known overlaps with one
  // another (item 4).
  const bounds = engine.boundaries;
  const witnessed = bounds
    .witnessedCoversOf(boundary)
    .filter((cover) => cover.length > 0 && cover.every((c) => bounds.isAtomic(c)));
  const settled = (cover: readonly string[]): boolean =>
    cover.every((a, i) => cover.slice(i + 1).every((b) => bounds.meetStatus(a, b).kind !== "unknown"));
  const atomicCover = witnessed.find(settled);

  if (atomicCover === undefined) {
    if (witnessed.length > 0) {
      return {
        ok: false,
        reason: `UL-Classical (C3) requires an atomic cover of "${boundary}" whose cells have known overlaps; register their disjointness.`,
      };
    }
    const unverified = bounds
      .registeredCovers()
      .find((c) => c.target === boundary && bounds.coverValidity(c.id).kind === "unverified");
    if (unverified !== undefined) {
      return {
        ok: false,
        reason: `UL-Classical (C3) requires a valid cover; the cover "${unverified.id}" of "${boundary}" is unverified and witnesses nothing.`,
      };
    }
    return {
      ok: false,
      reason: `Boundary "${boundary}" is neither atomic nor covered by a witnessed finite atomic partition.`,
    };
  }

  // (C3): every quantifier domain D the items use has a witnessed CloseDomain(D), is non-empty,
  // and satisfies Dom(D) ⊆ Dom(B*) for every atomic cell B*.
  for (const d of quantifierDomains) {
    if (!engine.isDomainClosed(d)) {
      return {
        ok: false,
        reason: `UL-Classical (C3) requires a witnessed CloseDomain("${d}") for every quantifier domain.`,
      };
    }
    const dom = engine.boundaries.handlesOf(d);
    if (dom.length === 0) {
      return {
        ok: false,
        reason: `UL-Classical (C3) requires non-empty quantifier domains; Dom("${d}") is empty.`,
      };
    }
    for (const cell of atomicCover) {
      const cellDom = new Set(engine.boundaries.handlesOf(cell).map((h) => h.id));
      const outside = dom.find((h) => !cellDom.has(h.id));
      if (outside !== undefined) {
        return {
          ok: false,
          reason: `UL-Classical (C3) requires Dom("${d}") ⊆ Dom("${cell}"); handle "${outside.id}" lies outside.`,
        };
      }
    }
  }

  // (C3): every handle the items name outside a quantifier belongs to Dom(B*) of every atomic cell,
  // which also refuses unbound variables.
  const freeHandles = (item: Item, bound: ReadonlySet<string>, out: Set<string>): void => {
    switch (item.kind) {
      case "atom":
        for (const r of item.roles) {
          if (!bound.has(r.handle)) {
            out.add(r.handle);
          }
        }
        return;
      case "equiv":
        for (const h of [item.left, item.right]) {
          if (!bound.has(h)) {
            out.add(h);
          }
        }
        return;
      case "flip":
        freeHandles(item.inner, bound, out);
        return;
      case "and":
      case "or":
        freeHandles(item.left, bound, out);
        freeHandles(item.right, bound, out);
        return;
      case "implies":
        freeHandles(item.antecedent, bound, out);
        freeHandles(item.consequent, bound, out);
        return;
      case "forall":
      case "exists": {
        const inner = new Set(bound).add(item.variable);
        freeHandles(item.body, inner, out);
        if (item.domainConstraint !== undefined) {
          freeHandles(item.domainConstraint, inner, out);
        }
        return;
      }
      default:
        return;
    }
  };
  const named = new Set<string>();
  for (const it of [...atoms, ...queryItems]) {
    freeHandles(it, new Set(), named);
  }
  for (const cell of atomicCover) {
    const outside = [...named].find((h) => engine.boundaries.getHandle(cell, h) === undefined);
    if (outside !== undefined) {
      return {
        ok: false,
        reason: `UL-Classical (C3) requires the items to name only handles of Dom("${cell}"); "${outside}" is not one.`,
      };
    }
  }

  // Enforce No-Gaps on all base atoms and congruences reachable across atoms and queryItems.
  for (const cell of atomicCover) {
    for (const a of allGroundAtoms) {
      const st = snap.localStatus(cell, a);
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
      const st = snap.localStatus(cell, item);
      if ((st === "Grounded" && pol === "-") || (st === "Excluded" && pol === "+")) {
        conflictReason ??= `UL-Classical valuation of "${itemKey(item)}" (${pol}) conflicts with existing "${st}" ground on atomic cell "${cell}".`;
      }
      return pol;
    };

    switch (item.kind) {
      case "atom": {
        const st = snap.localStatus(cell, item);
        return checkConsistent(st === "Grounded" ? "+" : "-");
      }
      case "bottom":
        return checkConsistent("-");
      case "equiv": {
        const st = snap.localStatus(cell, item);
        return checkConsistent(st === "Grounded" ? "+" : "-");
      }
      case "flip":
        return checkConsistent(evalOnAtomicCell(cell, item.inner) === "+" ? "-" : "+");
      // Both sides and every instance are evaluated, so a conflicting ground on any sub-item is
      // checked; nothing is short-circuited.
      case "and": {
        const left = evalOnAtomicCell(cell, item.left);
        const right = evalOnAtomicCell(cell, item.right);
        return checkConsistent(left === "+" && right === "+" ? "+" : "-");
      }
      case "or": {
        const left = evalOnAtomicCell(cell, item.left);
        const right = evalOnAtomicCell(cell, item.right);
        return checkConsistent(left === "+" || right === "+" ? "+" : "-");
      }
      case "implies": {
        // Under atomic-generated No-Gaps + No-Gluts closure, non-refuted conditionals close to +.
        const ant = evalOnAtomicCell(cell, item.antecedent);
        const con = evalOnAtomicCell(cell, item.consequent);
        return checkConsistent(ant === "+" && con === "-" ? "-" : "+");
      }
      case "forall":
      case "exists": {
        let some = false;
        let every = true;
        for (const h of engine.boundaries.handlesOf(item.domain)) {
          const inDomain =
            item.domainConstraint === undefined ||
            evalOnAtomicCell(cell, substituteHandle(item.domainConstraint, item.variable, h.id)) === "+";
          const value = evalOnAtomicCell(cell, substituteHandle(item.body, item.variable, h.id));
          if (inDomain) {
            some ||= value === "+";
            every &&= value === "+";
          }
        }
        return checkConsistent((item.kind === "forall" ? every : some) ? "+" : "-");
      }
      case "refl":
      case "ref":
        throw new Error(`UL-Classical requires level n = 0 closed formulas; found "${item.kind}".`);
    }
  };

  // (C4), (C6): the valuation agrees with every ground of Σ, not only the queried items. Every
  // level-0 item of U(Σ, Q) built from the considered atoms is checked, and every incompatibility
  // and structural collapse in force on a boundary above a cell.
  const consideredKeys = new Set(groundAtomMap.keys());
  const considered = (item: Item): boolean => {
    switch (item.kind) {
      case "atom":
      case "equiv":
        return consideredKeys.has(itemKey(item));
      case "bottom":
        return true;
      case "flip":
        return considered(item.inner);
      case "and":
      case "or":
        return considered(item.left) && considered(item.right);
      case "implies":
        return considered(item.antecedent) && considered(item.consequent);
      case "forall":
      case "exists": {
        const dom = engine.boundaries.handlesOf(item.domain);
        if (!engine.isDomainClosed(item.domain) || dom.length === 0) {
          return false;
        }
        if (!atomicCover.every((cell) => dom.every((h) => engine.boundaries.getHandle(cell, h.id) !== undefined))) {
          return false;
        }
        return dom.every(
          (h) =>
            considered(substituteHandle(item.body, item.variable, h.id)) &&
            (item.domainConstraint === undefined ||
              considered(substituteHandle(item.domainConstraint, item.variable, h.id))),
        );
      }
      default:
        return false;
    }
  };
  const trackedItems = snap.universe().filter(considered);
  for (const cell of atomicCover) {
    for (const it of trackedItems) {
      evalOnAtomicCell(cell, it);
    }
    for (const inc of engine.incompatibilitiesInForce()) {
      if (!engine.boundaries.refines(cell, inc.boundary) || !considered(inc.left) || !considered(inc.right)) {
        continue;
      }
      if (evalOnAtomicCell(cell, inc.left) === "+" && evalOnAtomicCell(cell, inc.right) === "+") {
        conflictReason ??= `UL-Classical valuation gives "+" to both sides of the incompatibility ${itemKey(inc.left)} ⊥ ${itemKey(inc.right)} on atomic cell "${cell}".`;
      }
    }
    for (const col of engine.collapsesInForce()) {
      if (engine.boundaries.refines(cell, col.boundary) && considered(col.item) && evalOnAtomicCell(cell, col.item) !== "-") {
        conflictReason ??= `UL-Classical valuation gives "+" to ${itemKey(col.item)}, which a structural collapse excludes on atomic cell "${cell}".`;
      }
    }
  }
  if (conflictReason !== undefined) {
    return { ok: false, reason: conflictReason };
  }

  // On a k-cell cover {B*_i} ▷ B, UL-Classical recovers the product Boolean algebra 2^k:
  // distinguish uniformly "+" (globally grounded), uniformly "-" (globally excluded), and "split".
  const results = new Map<string, ClassicalValuation>();
  for (const q of queryItems) {
    const cellPolarities = new Map<string, Polarity>();
    for (const cell of atomicCover) {
      cellPolarities.set(cell, evalOnAtomicCell(cell, q));
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
    if (conflictReason !== undefined) {
      return { ok: false, reason: conflictReason };
    }
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
