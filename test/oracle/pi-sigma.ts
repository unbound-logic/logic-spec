/**
 * Clean-room oracle for the evaluation program Π(Σ) of spec/core.md §5 item 14.
 *
 * Written from the specification alone (spec/core.md, AGENTS.md, and the design-review
 * entries `audit-spec-kernel-coupling`, `audit-universal-existential-import`,
 * `audit-unregistered-meet-closed-world` and `audit-cover-non-vacuity-drift`). It imports
 * only the item syntax of src/syntax.ts and the base queries of the boundary system in
 * src/boundary.ts (nonEmptyBoundaries, refines, meetStatus, handlesOf, isAdmissibleHandle,
 * hasNativeRelation, registeredCovers). It never reads or calls the reference kernel, nor the
 * boundary system's own cover closure and cover validity check, so the two can be compared by
 * differential testing.
 *
 * The oracle grounds Π(Σ) over the finite universe 𝔅(Σ) × U(Σ, Q) and computes its
 * well-founded model with the alternating fixpoint (Van Gelder 1989; Van Gelder, Ross and
 * Schlipf 1991). Every rule row of the item 14 table is implemented except two, which are
 * left out on purpose:
 *   - Theorem: the state description carries no recorded theorems, so the row never fires.
 *   - The reflection value of the Structural row (item 3): reflection items receive no
 *     structural value; they take part only in the rules that apply to every item
 *     (Base, downward heredity, Cover-Gluing, and as components of compounds) (A15).
 *
 * The readings this oracle chose where item 14 was ambiguous are recorded in
 * test/oracle/AMBIGUITIES.md; comments below cite those entries as "A<n>". The maintainer
 * ratified them, amending A3, A6 and A13 and the reporting rule (G4b), in the item 14 of
 * main commit 7b36043. The oracle follows item 14 as of main commit 9c0fd4d, which also
 * tracks ⊥ and the items of past transitions (A22, A23), and items 4 and 14 as of main commit
 * 5a385ce, which make overlap three-valued: Scoped Cut needs a known overlap, and opposite
 * records across an unknown overlap carry an OverlapUnknown obligation (A26–A32). It follows
 * items 5, 7 and 14 as amended in main commits fde28ec and a7377cf (main at c658e38): it judges
 * every registered cover valid, invalid or unverified, reports the obligations of the last two,
 * computes the witnessed covers as the registered covers that are not invalid closed under
 * Axioms 2–4, with a cell of unknown overlap blocking a base change, and reads Withdraw as
 * leaving a constraint out of the state while its items stay tracked (A33–A38). Since main
 * commit fe2b5cf (main at 826deb0), a derived cover is judged by the same rule and is not derived
 * when it is invalid (A37). Item 4 as amended in b5d5c5c makes a registered meet the greatest
 * lower bound of its pair; the oracle reads the inferred refinements through refines and
 * meetStatus, so its code is unchanged by it (A26, A39). Items 5 and 14 as amended in e869e9b
 * (branch b1-unverified above main at 306a2ff) make an unverified cover witness nothing, so the
 * closure starts from the valid registered covers only (A33, A36, A37), and let an ambiguous meet
 * stop Scoped Cut only for an instance whose Live premises are true in the least model of the
 * program read with every obs atom false and the instances over ambiguous pairs left out (A31,
 * A40).
 */

import { BOT_BOUNDARY, type BoundarySystem, type MeetStatus } from "../../src/boundary.ts";
import {
  atom,
  bottom,
  equiv,
  implies,
  itemKey,
  substituteHandle,
  type Item,
  type Polarity,
} from "../../src/syntax.ts";

/** Three-valued truth of an atom in the well-founded model. */
export type Truth = "true" | "undefined" | "false";

/** Local status of (B, A), read from its present records (item 14, Reporting). */
export type LocalStatus = "Open" | "Grounded" | "Excluded" | "Collision";

/** Authority of a present record (item 14, Reporting). */
export type Authority = "Live" | "Undetermined" | "Quarantined";

/** Base ground Observe±(B, A, w) in G±. */
export type PiObservation = {
  readonly boundary: string;
  readonly polarity: Polarity;
  readonly item: Item;
};

/** Material incompatibility A ⊥_B C registered in C_B. */
export type PiIncompatibility = {
  readonly boundary: string;
  readonly left: Item;
  readonly right: Item;
};

/** Structural collapse B ⊓ [A] = ⊥_B registered in C_B. */
export type PiCollapse = {
  readonly boundary: string;
  readonly item: Item;
};

/**
 * Explicit description of an inquiry state Σ and a query set Q. It lists what is in force: the
 * observations in G± and the constraints of C_B that are registered and not withdrawn (item 7,
 * Withdraw; item 14, Constraints). The covers in force are the boundary system's
 * registeredCovers(), from which Withdraw removes a cover by its identifier (A38).
 */
export type PiState = {
  readonly boundaries: BoundarySystem;
  readonly observations: readonly PiObservation[];
  /** Incompatibilities in force; a withdrawn one is left out and its items go to historyItems. */
  readonly incompatibilities?: readonly PiIncompatibility[];
  /** Structural collapses in force; a withdrawn one is left out and its items go to historyItems. */
  readonly collapses?: readonly PiCollapse[];
  /** Quantifier domains D whose closure CloseDomain(D) is witnessed in C_B and not withdrawn. */
  readonly closedDomains?: readonly string[];
  /** The queried items Q. */
  readonly queries?: readonly Item[];
  /**
   * Items named by past transitions of Σ that are no longer in force: the item of a retracted
   * observation (A23), both sides of a withdrawn incompatibility A ⊥_B C, and both A and A → ⊥
   * of a withdrawn collapse of A (A38). They are tracked, so they and their closure belong to
   * U(Σ, Q), but they supply no record and no constraint. The oracle derives nothing from
   * them, so the caller lists every item. A withdrawn cover or closure names boundaries, not
   * items, and adds none.
   */
  readonly historyItems?: readonly Item[];
};

export type PolarityPair<T> = { readonly "+": T; readonly "-": T };

/** The reported values of one slot (B, A). */
export type PiRow = {
  readonly boundary: string;
  readonly item: Item;
  readonly rec: PolarityPair<Truth>;
  readonly live: PolarityPair<Truth>;
  readonly coll: Truth;
  readonly obs: Truth;
  /** A record is present when rec is true (G4b); an undefined record is possible only. */
  readonly present: PolarityPair<boolean>;
  readonly localStatus: LocalStatus;
  /** Authority of each present record; null when the record is absent. */
  readonly authority: PolarityPair<Authority | null>;
  /** Rev(B, A): carried by every (B, A) in Collision. */
  readonly revisionObligation: boolean;
};

/**
 * OverlapUnknown(B₁, B₂, A) (item 14, Reporting): the overlap of `left` and `right` is unknown
 * (item 4), and one of them holds a present +A record while the other holds a present -A
 * record. Each unordered pair is reported once per item, with `left` listed before `right` in
 * PiModel.boundaries (A28).
 */
export type PiOverlapObligation = {
  readonly left: string;
  readonly right: string;
  readonly item: Item;
};

/**
 * The revision obligation item 5 attaches to an invalid or unverified registered cover (A34). It
 * names the cover and the sub-boundaries B' ⊑ target that its validity rests on; settling their
 * overlaps or withdrawing the cover discharges it.
 */
export type PiCoverObligation = {
  /** The identifier the cover was registered under by WitnessCover, which Withdraw names. */
  readonly id: string;
  readonly target: string;
  /** The cells as registered. */
  readonly cells: readonly string[];
  readonly validity: "invalid" | "unverified";
  /**
   * In the order of PiModel.boundaries: for an invalid cover, every B' disjoint from every cell
   * (the boundaries that refute it); for an unverified cover, every B' known to overlap no cell
   * and of unknown overlap with at least one (the boundaries that leave it unsettled).
   */
  readonly subBoundaries: readonly string[];
};

/** A witnessed cover {cells} ▷ boundary that no witnessed cover of boundary with fewer cells contains (A36). */
export type PiWitnessedCover = {
  readonly boundary: string;
  /** In the order of PiModel.boundaries. */
  readonly cells: readonly string[];
};

export type PiModel = {
  /** 𝔅(Σ), in the order the boundary system lists them. */
  readonly boundaries: readonly string[];
  /** U(Σ, Q). */
  readonly universe: readonly Item[];
  /** One row for every B in 𝔅(Σ) and A in U(Σ, Q). */
  readonly rows: readonly PiRow[];
  readonly revisionObligations: readonly { readonly boundary: string; readonly item: Item }[];
  /**
   * The OverlapUnknown obligations, sorted by `left`, then `right` (both in the order of
   * `boundaries`), then the item's place in `universe` (A28, A29). They are separate from the
   * Rev(B, A) obligations and change no local status.
   */
  readonly overlapObligations: readonly PiOverlapObligation[];
  /**
   * The ⊆-minimal witnessed covers of every boundary of 𝔅(Σ), the identity covers {B} included,
   * sorted by boundary, then by cells (A36). They give every cover rule instance of Π(Σ); a
   * witnessed cover not listed is a superset of a listed cover of the same boundary.
   */
  readonly witnessedCovers: readonly PiWitnessedCover[];
  /**
   * One obligation for every invalid or unverified registered cover, in registration order
   * (A34). Separate from the Rev(B, A) and OverlapUnknown obligations; changes no local status.
   */
  readonly coverObligations: readonly PiCoverObligation[];
  /** Number of applications of the Gelfond–Lifschitz-style operator Γ. */
  readonly rounds: number;
  /** The row of (boundary, item); throws when the slot is outside 𝔅(Σ) × U(Σ, Q). */
  at(boundary: string, item: Item): PiRow;
};

const POLARITIES: readonly Polarity[] = ["+", "-"];

/**
 * Bound on the witnessed covers of one state, minimal or not. It is not semantics: past it the
 * oracle reports an error instead of a truncated closure (item 14, Role; A36).
 */
const MAX_WITNESSED_COVERS = 20_000;

/** Bound on the combinations Transitivity forms in one state; like the cover bound, not semantics. */
const MAX_COVER_COMBINATIONS = 2_000_000;

function opposite(p: Polarity): Polarity {
  return p === "+" ? "-" : "+";
}

/**
 * U(Σ, Q): the tracked and queried items, closed under direct sub-items, quantifier
 * instances A(w) and δ(w) for w ∈ Dom(D), and congruence rewrites at one position by the
 * handles of the boundaries in 𝔅(Σ). A polarity flip belongs to U(Σ, Q) whenever it arises
 * this way (A3, as amended by item 14); U(Σ, Q) is never closed under prefixing `~`.
 */
export function buildUniverse(
  bs: BoundarySystem,
  boundaries: readonly string[],
  tracked: readonly Item[],
  queries: readonly Item[],
): Item[] {
  // A5: rewrites use the handles of every boundary in 𝔅(Σ).
  const handles = [
    ...new Set(boundaries.flatMap((b) => bs.handlesOf(b).map((h) => h.id))),
  ].sort();

  const items: Item[] = [];
  const seen = new Set<string>();
  const work: Item[] = [];
  const add = (item: Item): void => {
    const key = itemKey(item);
    if (seen.has(key)) {
      return;
    }
    seen.add(key);
    items.push(item);
    work.push(item);
  };

  for (const item of [...tracked, ...queries]) {
    add(item);
  }
  for (let next = work.pop(); next !== undefined; next = work.pop()) {
    const item = next;
    switch (item.kind) {
      case "flip":
        add(item.inner);
        break;
      case "and":
      case "or":
        add(item.left);
        add(item.right);
        break;
      case "implies":
        add(item.antecedent);
        add(item.consequent);
        break;
      case "forall":
      case "exists": {
        // A4: a quantifier's sub-items are its instances; the open body is not an item.
        // A25: Dom(D) is whatever the boundary system admits.
        const constraint = item.domainConstraint;
        for (const h of bs.handlesOf(item.domain)) {
          add(substituteHandle(item.body, item.variable, h.id));
          if (constraint !== undefined) {
            add(substituteHandle(constraint, item.variable, h.id));
          }
        }
        break;
      }
      case "atom":
        // A5: position-wise rewrites, iterated through the worklist.
        item.roles.forEach((_, position) => {
          for (const u of handles) {
            add(
              atom(
                item.relation,
                item.roles.map((r, j) => (j === position ? { role: r.role, handle: u } : r)),
              ),
            );
          }
        });
        break;
      case "equiv":
        bs.handlesOf(item.boundary); // throws on an undeclared boundary
        for (const u of handles) {
          add(equiv(item.boundary, u, item.right));
          add(equiv(item.boundary, item.left, u));
        }
        break;
      case "bottom":
      case "refl":
      case "ref":
        // A4: reflection and named references have no direct sub-items here.
        break;
    }
  }
  return items;
}

/** A premise of a rule instance: a record premise (live = false) or a Live premise. */
type Prem = {
  readonly b: number;
  readonly p: Polarity;
  /** Index of the premise item in U(Σ, Q); undefined when the item is outside U. */
  readonly a: number | undefined;
  readonly live: boolean;
};
/** A conjunction of premises. */
type Alt = readonly Prem[];
/** A requirement met by any one of its alternatives. */
type Req = readonly Alt[];

type Interpretation = {
  readonly truth: Uint8Array;
  readonly coll: Uint8Array;
  readonly obs: Uint8Array;
};

/** Compute the well-founded model of Π(Σ) and report it as item 14 prescribes. */
export function evaluatePi(state: PiState): PiModel {
  const bs = state.boundaries;
  const incompatibilities = state.incompatibilities ?? [];
  const collapses = state.collapses ?? [];
  const queries = state.queries ?? [];
  const closedDomains = new Set(state.closedDomains ?? []);

  // ---------------------------------------------------------------- 𝔅(Σ) (A1)
  const boundaries = [...bs.nonEmptyBoundaries()];
  const nb = boundaries.length;
  const bIndex = new Map(boundaries.map((b, i) => [b, i] as const));
  const boundaryIndex = (name: string, role: string): number => {
    const i = bIndex.get(name);
    if (i === undefined) {
      throw new Error(`Π(Σ) oracle: ${role} "${name}" is not a non-empty boundary declared in Σ.`);
    }
    return i;
  };
  const boundaryName = (b: number): string => {
    const name = boundaries[b];
    if (name === undefined) {
      throw new Error(`Π(Σ) oracle: internal error, boundary index ${b} out of range.`);
    }
    return name;
  };

  for (const o of state.observations) {
    boundaryIndex(o.boundary, "observation boundary");
    if (o.polarity === "+" && o.item.kind === "bottom") {
      // A16: item 12 requires ⊥ ∉ G⁺; such a state is not a valid Σ.
      throw new Error("Π(Σ) oracle: item 12 requires ⊥ ∉ G⁺ on every non-empty boundary.");
    }
  }
  for (const c of incompatibilities) {
    boundaryIndex(c.boundary, "incompatibility boundary");
  }
  for (const c of collapses) {
    boundaryIndex(c.boundary, "collapse boundary");
  }
  for (const d of closedDomains) {
    // A14: a listed closure is taken as valid for the current Dom(D).
    bs.handlesOf(d); // throws on an undeclared boundary
  }

  // ---------------------------------------------------------------- U(Σ, Q) (A2–A5)
  const tracked: Item[] = [
    ...state.observations.map((o) => o.item),
    ...incompatibilities.flatMap((c) => [c.left, c.right]),
    ...collapses.flatMap((c) => [c.item, implies(c.item, bottom())]),
    // A23: items of past transitions stay tracked after a retraction.
    ...(state.historyItems ?? []),
    // A22: ⊥ is always tracked.
    bottom(),
  ];
  const universe = buildUniverse(bs, boundaries, tracked, queries);
  const nu = universe.length;
  const uIndex = new Map(universe.map((item, i) => [itemKey(item), i] as const));
  const idx = (item: Item): number | undefined => uIndex.get(itemKey(item));

  // ---------------------------------------------------------------- atoms
  const nS = nb * nu;
  const slot = (b: number, a: number): number => b * nu + a;
  const recAtom = (p: Polarity, s: number): number => (p === "+" ? 0 : nS) + s;
  const liveAtom = (p: Polarity, s: number): number => 2 * nS + (p === "+" ? 0 : nS) + s;

  const refinesTable = new Uint8Array(nb * nb);
  for (let sub = 0; sub < nb; sub++) {
    for (let sup = 0; sup < nb; sup++) {
      refinesTable[sub * nb + sup] = bs.refines(boundaryName(sub), boundaryName(sup)) ? 1 : 0;
    }
  }
  const isSub = (sub: number, sup: number): boolean => refinesTable[sub * nb + sup] === 1;
  const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
  const allB = range(nb);
  const subsOf = allB.map((sup) => allB.filter((sub) => isSub(sub, sup)));
  const subsOfName = new Map<string, number[]>();
  const subsOfAnyBoundary = (name: string): number[] => {
    let subs = subsOfName.get(name);
    if (subs === undefined) {
      subs = allB.filter((b) => bs.refines(boundaryName(b), name));
      subsOfName.set(name, subs);
    }
    return subs;
  };

  // A26: overlap is three-valued (item 4) and read from BoundarySystem.meetStatus. The oracle
  // never calls `meet`, which gives ⊥_B for an unknown overlap as well as for disjointness.
  // A31: an ambiguous meet (several maximal common sub-boundaries) is an error, raised only
  // where item 14's Role says a rule instance, a cover or the reporting needs that pair's status.
  type PairMeet =
    | { readonly kind: "overlap"; readonly meet: number }
    | { readonly kind: "disjoint" }
    | { readonly kind: "unknown" };
  type PairMeetOrAmbiguous = PairMeet | { readonly kind: "ambiguous"; readonly reason: string };
  const meetCache = new Map<number, PairMeetOrAmbiguous>();
  const pairMeet = (b1: number, b2: number): PairMeetOrAmbiguous => {
    // meetStatus is symmetric, so the cache is keyed by the unordered pair.
    const key = Math.min(b1, b2) * nb + Math.max(b1, b2);
    const cached = meetCache.get(key);
    if (cached !== undefined) {
      return cached;
    }
    let status: MeetStatus;
    try {
      status = bs.meetStatus(boundaryName(b1), boundaryName(b2));
    } catch (error) {
      // Both boundaries are declared, so meetStatus throws only for an ambiguous meet.
      const reason = error instanceof Error ? error.message : String(error);
      const ambiguous = { kind: "ambiguous", reason } as const;
      meetCache.set(key, ambiguous);
      return ambiguous;
    }
    const result: PairMeet =
      status.kind === "overlap" ? { kind: "overlap", meet: boundaryIndex(status.meet, "meet") } : status;
    meetCache.set(key, result);
    return result;
  };
  /** The status of a pair that `purpose` needs; an ambiguous meet stops the oracle (A11, A31). */
  const neededMeet = (b1: number, b2: number, purpose: string): PairMeet => {
    const result = pairMeet(b1, b2);
    if (result.kind === "ambiguous") {
      throw new Error(
        `Π(Σ) oracle: ${purpose} needs the meet of "${boundaryName(b1)}" and "${boundaryName(b2)}", which is ambiguous (${result.reason}).`,
      );
    }
    return result;
  };

  // ---------------------------------------------------------------- witnessed covers (item 5)
  // Item 5 as amended in a7377cf, fe2b5cf and e869e9b: every registered cover is judged against
  // the current boundaries (A33), an invalid or unverified one witnesses nothing, and the witnessed
  // covers are the valid registered covers, closed under Axioms 2–4, where a derived cover is
  // judged by the same rule and is not derived when it is invalid (A36, A37). The oracle computes
  // this itself from BoundarySystem.registeredCovers() and meetStatus (A26); it never calls the
  // boundary system's own cover closure or validity check (A10 as superseded).
  const byIndex = (x: number, y: number): number => x - y;
  const describeCover = (target: number, cells: readonly number[]): string =>
    `{${cells.map(boundaryName).join(", ")}} ▷ ${boundaryName(target)}`;

  type CoverJudgement = {
    readonly refuting: readonly number[];
    readonly unsettled: readonly number[];
    readonly undecided?: { readonly sub: number; readonly cell: number; readonly reason: string };
  };
  /**
   * Item 5's validity rule for the family `cells` covering `target` (A33). B' ⊑ target ranges over
   * 𝔅(Σ), target included. B' refutes the family when it is disjoint from every cell (so the empty
   * family is refuted by target itself), and leaves it unsettled when it is known to overlap no
   * cell and has an unknown overlap with one. A35: a B' with no known overlap and an ambiguous
   * meet with a cell is undecided; it is never disjoint from that cell, so it never refutes.
   */
  const judgeCover = (target: number, cells: readonly number[]): CoverJudgement => {
    const refuting: number[] = [];
    const unsettled: number[] = [];
    let undecided: CoverJudgement["undecided"];
    for (const sub of subsOf[target] ?? []) {
      let overlap = false;
      let unknown = false;
      let ambiguous: { readonly cell: number; readonly reason: string } | undefined;
      for (const c of cells) {
        const m = pairMeet(sub, c);
        if (m.kind === "overlap") {
          overlap = true;
          break;
        }
        if (m.kind === "unknown") {
          unknown = true;
        } else if (m.kind === "ambiguous") {
          ambiguous ??= { cell: c, reason: m.reason };
        }
      }
      if (overlap) {
        continue;
      }
      if (ambiguous !== undefined) {
        undecided ??= { sub, ...ambiguous };
      } else if (unknown) {
        unsettled.push(sub);
      } else {
        refuting.push(sub);
      }
    }
    return undecided === undefined ? { refuting, unsettled } : { refuting, unsettled, undecided };
  };

  const coverObligations: PiCoverObligation[] = [];
  const seeds: { readonly target: number; readonly cells: readonly number[] }[] = [];
  for (const cover of bs.registeredCovers()) {
    if (cover.target === BOT_BOUNDARY) {
      // A33: ⊥_B has no row and no non-empty sub-boundary to judge a cover of it by.
      continue;
    }
    const target = boundaryIndex(cover.target, `target of cover "${cover.id}"`);
    const cellSet = new Set<number>();
    for (const cell of cover.cells) {
      if (cell === BOT_BOUNDARY) {
        // A33: a ⊥_B cell is disjoint from every boundary, and ∅ ▷ ⊥_B (Axiom 2) lets
        // Transitivity drop it, so it is judged as disjoint and left out of the witnessed cover.
        continue;
      }
      const c = boundaryIndex(cell, `cell of cover "${cover.id}"`);
      if (!isSub(c, target)) {
        // A16: Axiom 1 (Refinement) is a registration condition; such a state is not a valid Σ.
        throw new Error(
          `Π(Σ) oracle: the registered cover "${cover.id}" breaks Axiom 1 of item 5: "${cell}" does not refine "${cover.target}".`,
        );
      }
      cellSet.add(c);
    }
    const cells = [...cellSet].sort(byIndex);
    const { refuting, unsettled, undecided } = judgeCover(target, cells);

    // A34: one obligation per invalid or unverified registered cover, naming it and the
    // sub-boundaries its validity rests on.
    const registered = { id: cover.id, target: cover.target, cells: [...cover.cells] };
    if (refuting.length > 0) {
      coverObligations.push({
        ...registered,
        validity: "invalid",
        subBoundaries: refuting.map(boundaryName),
      });
      continue; // an invalid cover witnesses nothing, and no cover is derived from it
    }
    if (undecided !== undefined) {
      // A35: the obligation tells an unverified cover from a valid one, and B' decides it.
      throw new Error(
        `Π(Σ) oracle: judging the cover "${cover.id}" (item 5) needs the meet of "${boundaryName(undecided.sub)}" and "${boundaryName(undecided.cell)}", which is ambiguous (${undecided.reason}).`,
      );
    }
    if (unsettled.length > 0) {
      coverObligations.push({
        ...registered,
        validity: "unverified",
        subBoundaries: unsettled.map(boundaryName),
      });
      // e869e9b (audit-unverified-cover-authority): an unverified cover witnesses nothing either,
      // and seeds no derived cover, while it keeps its obligation (A33, A36).
      continue;
    }
    seeds.push({ target, cells }); // only valid registered covers seed the closure
  }

  // A36: the closure is computed in full, from the valid registered covers and the identity
  // covers. It keeps every witnessed cover, minimal or not, as item 5 defines the closure, and only
  // the rule instances and PiModel.witnessedCovers use the minimal ones. Each cover records the
  // pass that admitted it, so every combination of Axiom 4 is formed once (semi-naive evaluation).
  type CoverEntry = { readonly cells: readonly number[]; readonly pass: number };
  const coverKey = (cells: readonly number[]): string => cells.join(",");
  // Axiom 2 (Identity): {B} ▷ B for every B ∈ 𝔅(Σ); it is valid, since every B' ⊑ B refines B.
  const coverSets: Map<string, CoverEntry>[] = allB.map(
    (b) => new Map([[coverKey([b]), { cells: [b], pass: 0 }]]),
  );
  const coversAt = (b: number): Map<string, CoverEntry> => {
    const covers = coverSets[b];
    if (covers === undefined) {
      throw new Error(`Π(Σ) oracle: internal error, boundary index ${b} out of range.`);
    }
    return covers;
  };
  let pass = 0;
  let coverCount = nb;
  const admit = (target: number, cells: readonly number[]): boolean => {
    const covers = coversAt(target);
    const key = coverKey(cells);
    if (covers.has(key)) {
      return false;
    }
    covers.set(key, { cells, pass });
    coverCount += 1;
    if (coverCount > MAX_WITNESSED_COVERS) {
      throw new Error(
        `Π(Σ) oracle: the witnessed covers exceed ${MAX_WITNESSED_COVERS}; reporting an error instead of a truncated closure (item 14, Role).`,
      );
    }
    return true;
  };
  for (const { target, cells } of seeds) {
    admit(target, cells);
  }
  /**
   * A37: a derived cover, from Transitivity or a base change, joins the closure unless item 5's
   * rule judges it invalid, whatever its source. Since e869e9b every source is valid, and item 5
   * states that covers derived from valid registered covers are valid, so the check should never
   * reject one; the oracle keeps it rather than rely on that sentence (A37, A39).
   * Admission never needs an ambiguous meet, since an ambiguous pair never refutes (A35).
   */
  const admitDerived = (target: number, cells: readonly number[]): boolean => {
    if (coversAt(target).has(coverKey(cells))) {
      return false;
    }
    if (judgeCover(target, cells).refuting.length > 0) {
      return false; // an invalid derived cover is not derived, and nothing is derived from it
    }
    return admit(target, cells);
  };

  let combinations = 0;
  for (let changed = true; changed; ) {
    changed = false;
    pass += 1;
    // Covers admitted in the previous pass are fresh; covers admitted in this pass wait.
    const fresh = pass - 1;
    const known = allB.map((b) => [...coversAt(b).values()].filter((e) => e.pass <= fresh));
    const knownAt = (b: number): readonly CoverEntry[] => known[b] ?? [];
    for (const b of allB) {
      for (const outer of knownAt(b)) {
        const cells = outer.cells;
        // Axiom 4 (Transitivity): from {Bᵢ} ▷ B and a witnessed cover of every Bᵢ (its identity
        // cover included), the union of the chosen covers covers B. A combination is new when one
        // of its covers is fresh; it is formed at the first fresh position only.
        if (!(cells.length === 1 && cells[0] === b)) {
          const options = cells.map((c) => knownAt(c));
          const chosen: (readonly number[])[] = [];
          const visit = (i: number, firstFresh: number): void => {
            if (i === cells.length) {
              combinations += 1;
              if (combinations > MAX_COVER_COMBINATIONS) {
                throw new Error(
                  `Π(Σ) oracle: Transitivity forms more than ${MAX_COVER_COMBINATIONS} combinations of covers; reporting an error instead of a truncated closure (item 14, Role).`,
                );
              }
              const union = [...new Set(chosen.flat())].sort(byIndex);
              if (admitDerived(b, union)) {
                changed = true;
              }
              return;
            }
            for (const entry of options[i] ?? []) {
              if (i < firstFresh && entry.pass === fresh) {
                continue;
              }
              if (i === firstFresh && entry.pass !== fresh) {
                continue;
              }
              chosen.push(entry.cells);
              visit(i + 1, firstFresh);
              chosen.pop();
            }
          };
          if (outer.pass === fresh) {
            visit(0, -1);
          } else {
            for (let first = 0; first < cells.length; first++) {
              visit(0, first);
            }
          }
        }
        // Axiom 3 (Meet-Stability): {Bᵢ ⊓ B' | Bᵢ known to overlap B'} ▷ B' for B' ⊑ B, when every
        // cell is known to overlap B' or disjoint from it; a cell of unknown overlap blocks it.
        if (outer.pass !== fresh) {
          continue;
        }
        for (const sub of subsOf[b] ?? []) {
          if (sub === b) {
            continue;
          }
          const meets = new Set<number>();
          let blocked = false;
          let ambiguous: { readonly cell: number; readonly reason: string } | undefined;
          for (const c of cells) {
            const m = pairMeet(c, sub);
            if (m.kind === "unknown") {
              blocked = true;
              break;
            }
            if (m.kind === "ambiguous") {
              ambiguous ??= { cell: c, reason: m.reason };
            } else if (m.kind === "overlap") {
              meets.add(m.meet);
            }
          }
          if (blocked) {
            continue;
          }
          if (ambiguous !== undefined) {
            // A35: the base change of a witnessed cover is part of the closure and needs this meet.
            throw new Error(
              `Π(Σ) oracle: the base change of ${describeCover(b, cells)} to ${boundaryName(sub)} (item 5, Axiom 3) needs the meet of "${boundaryName(ambiguous.cell)}" and "${boundaryName(sub)}", which is ambiguous (${ambiguous.reason}).`,
            );
          }
          if (meets.size === 0) {
            // A37: B' would be disjoint from every cell, so the cover would be invalid; no witnessed
            // cover is, so item 5's "no base change is empty" holds and this cannot happen.
            throw new Error(
              `Π(Σ) oracle: internal error, the witnessed cover ${describeCover(b, cells)} has an empty base change to ${boundaryName(sub)}.`,
            );
          }
          if (admitDerived(sub, [...meets].sort(byIndex))) {
            changed = true;
          }
        }
      }
    }
  }

  const isSubset = (small: readonly number[], large: readonly number[]): boolean => {
    let j = 0;
    for (const x of small) {
      while (j < large.length && (large[j] ?? -1) < x) {
        j++;
      }
      if (large[j] !== x) {
        return false;
      }
      j++;
    }
    return true;
  };
  const compareCells = (x: readonly number[], y: readonly number[]): number => {
    for (let i = 0; i < Math.min(x.length, y.length); i++) {
      const d = (x[i] ?? 0) - (y[i] ?? 0);
      if (d !== 0) {
        return d;
      }
    }
    return x.length - y.length;
  };
  // A36: a cover rule instance over a witnessed cover that contains a smaller witnessed cover of
  // the same boundary has more premises than the smaller one's and never changes the model, so the
  // program uses the minimal witnessed covers. No minimal cover other than {B} holds B itself.
  const coversOf = allB.map((b) => {
    const all = [...coversAt(b).values()].map((e) => e.cells);
    return all
      .filter((cells) => !all.some((other) => other.length < cells.length && isSubset(other, cells)))
      .sort(compareCells);
  });
  const witnessedCovers: PiWitnessedCover[] = allB.flatMap((b) =>
    (coversOf[b] ?? []).map((cells) => ({ boundary: boundaryName(b), cells: cells.map(boundaryName) })),
  );

  // ---------------------------------------------------------------- ground program
  const heads: number[] = [];
  const bodies: number[][] = [];
  /** Slot whose obs atom must be false for the clause to apply, or -1. */
  const guards: number[] = [];
  let atomCount = 4 * nS;
  const addClause = (head: number, body: number[], guard: number): void => {
    heads.push(head);
    bodies.push(body);
    guards.push(guard);
  };
  const premSlot = (pr: Prem): number => {
    if (pr.a === undefined) {
      throw new Error("Π(Σ) oracle: internal error, unresolved premise.");
    }
    return slot(pr.b, pr.a);
  };
  const premRec = (pr: Prem): number =>
    pr.live ? liveAtom(pr.p, premSlot(pr)) : recAtom(pr.p, premSlot(pr));
  const premLive = (pr: Prem): number => liveAtom(pr.p, premSlot(pr));

  /**
   * One rule instance with conclusion (b, p, a). For record premises R and Live premises L:
   *   rec(b, p, a)  ← rec(P) for P ∈ R, live(P) for P ∈ L
   *   live(b, p, a) ← live(P) for P ∈ R ∪ L, not obs(b, a)
   * A requirement with several alternatives stands for one instance per choice; it is
   * compiled through an auxiliary atom defined by positive clauses only, which leaves the
   * well-founded model of the original atoms unchanged.
   */
  const emit = (b: number, p: Polarity, a: number | undefined, reqs: readonly Req[]): void => {
    if (a === undefined) {
      return; // A17: the conclusion is outside U(Σ, Q), so the instance has no atom
    }
    const usable: Alt[][] = [];
    for (const req of reqs) {
      // A17: a premise outside U(Σ, Q) has no atom and can never hold.
      const alts = req.filter((alt) => alt.every((pr) => pr.a !== undefined));
      if (alts.length === 0) {
        return;
      }
      usable.push(alts);
    }
    const s = slot(b, a);
    const recBody: number[] = [];
    const liveBody: number[] = [];
    for (const alts of usable) {
      const only = alts.length === 1 ? alts[0] : undefined;
      if (only !== undefined) {
        for (const pr of only) {
          recBody.push(premRec(pr));
          liveBody.push(premLive(pr));
        }
        continue;
      }
      const auxRec = atomCount++;
      const auxLive = atomCount++;
      for (const alt of alts) {
        addClause(auxRec, alt.map(premRec), -1);
        addClause(auxLive, alt.map(premLive), -1);
      }
      recBody.push(auxRec);
      liveBody.push(auxLive);
    }
    addClause(recAtom(p, s), recBody, -1);
    addClause(liveAtom(p, s), liveBody, s);
  };
  const R = (b: number, p: Polarity, a: number | undefined): Prem => ({ b, p, a, live: false });
  const L = (b: number, p: Polarity, a: number | undefined): Prem => ({ b, p, a, live: true });
  const each = (...prems: Prem[]): Req[] => prems.map((pr) => [[pr]]);

  // Base: Observe±(B, A, w) in G±.
  for (const o of state.observations) {
    emit(boundaryIndex(o.boundary, "observation boundary"), o.polarity, idx(o.item), []);
  }

  // Structural: (B, -, ⊥) always.
  const bottomIdx = idx(bottom());
  if (bottomIdx !== undefined) {
    for (const b of allB) {
      emit(b, "-", bottomIdx, []);
    }
  }
  // Structural: (B, +, A → ⊥) and (B, -, A) when B ⊓ [A] = ⊥_B in C_B (A8).
  for (const c of collapses) {
    const b = boundaryIndex(c.boundary, "collapse boundary");
    emit(b, "+", idx(implies(c.item, bottom())), []);
    emit(b, "-", idx(c.item), []);
  }

  // Downward heredity: (B', p, A) from record (B, p, A), B' ⊑ B (B' = B adds nothing).
  for (const b of allB) {
    for (const sub of subsOf[b] ?? []) {
      if (sub === b) {
        continue;
      }
      for (let a = 0; a < nu; a++) {
        for (const p of POLARITIES) {
          emit(sub, p, a, each(R(b, p, a)));
        }
      }
    }
  }

  // Item-shape rules.
  /** A Scoped Cut instance over an ambiguous pair: Live (b1, +, antecedent), Live (b2, +, implication). */
  type AmbiguousCut = {
    readonly b1: number;
    readonly b2: number;
    readonly antecedent: number;
    readonly implication: number;
    readonly reason: string;
  };
  const ambiguousCuts: AmbiguousCut[] = [];
  type Equiv = Extract<Item, { kind: "equiv" }>;
  type RelAtom = Extract<Item, { kind: "atom" }>;
  const equivs: { readonly item: Equiv; readonly a: number }[] = [];
  const relAtoms: { readonly item: RelAtom; readonly a: number; readonly handles: Set<string> }[] = [];
  /** antecedent key → (consequent key → implication index) */
  const implicationsByAntecedent = new Map<string, Map<string, number>>();
  universe.forEach((item, a) => {
    if (item.kind === "equiv") {
      equivs.push({ item, a });
    } else if (item.kind === "atom") {
      relAtoms.push({ item, a, handles: new Set(item.roles.map((r) => r.handle)) });
    } else if (item.kind === "implies") {
      const key = itemKey(item.antecedent);
      const byConsequent = implicationsByAntecedent.get(key) ?? new Map<string, number>();
      byConsequent.set(itemKey(item.consequent), a);
      implicationsByAntecedent.set(key, byConsequent);
    }
  });

  universe.forEach((item, a) => {
    switch (item.kind) {
      case "flip": {
        // Polarity flip: (B, p̄, ~A) from record (B, p, A); (B, p̄, A) from record (B, p, ~A).
        const inner = idx(item.inner);
        for (const b of allB) {
          for (const p of POLARITIES) {
            emit(b, opposite(p), a, each(R(b, p, inner)));
            emit(b, opposite(p), inner, each(R(b, p, a)));
          }
        }
        break;
      }
      case "and": {
        const left = idx(item.left);
        const right = idx(item.right);
        for (const b of allB) {
          // ∧I; ∧E
          emit(b, "+", a, each(L(b, "+", left), L(b, "+", right)));
          emit(b, "+", left, each(L(b, "+", a)));
          emit(b, "+", right, each(L(b, "+", a)));
          // ∧ exclusion: record (B, -, A) or record (B, -, C)
          emit(b, "-", a, each(R(b, "-", left)));
          emit(b, "-", a, each(R(b, "-", right)));
        }
        break;
      }
      case "or": {
        const left = idx(item.left);
        const right = idx(item.right);
        for (const b of allB) {
          // ∨ by cover, including the identity cover {B} (A10).
          for (const cells of coversOf[b] ?? []) {
            emit(
              b,
              "+",
              a,
              cells.map((c) => [[L(c, "+", left)], [L(c, "+", right)]]),
            );
          }
          // ∨ exclusion
          emit(b, "-", a, each(R(b, "-", left), R(b, "-", right)));
        }
        // ∨E for every E with A → E and C → E in U(Σ, Q) (A20).
        const fromLeft = implicationsByAntecedent.get(itemKey(item.left));
        const fromRight = implicationsByAntecedent.get(itemKey(item.right));
        if (fromLeft !== undefined && fromRight !== undefined) {
          for (const [eKey, leftImpl] of fromLeft) {
            const rightImpl = fromRight.get(eKey);
            if (rightImpl === undefined) {
              continue;
            }
            const e = uIndex.get(eKey);
            for (const b of allB) {
              emit(b, "+", e, each(L(b, "+", a), L(b, "+", leftImpl), L(b, "+", rightImpl)));
            }
          }
        }
        break;
      }
      case "implies": {
        const antecedent = idx(item.antecedent);
        const consequent = idx(item.consequent);
        // Scoped Cut: (B₁ ⊓ B₂, +, C) from Live (B₁, +, A), Live (B₂, +, A → C), only when B₁
        // and B₂ are known to overlap; a disjoint or unknown overlap licenses nothing (A26, A27).
        // An instance over an ambiguous pair has no conclusion boundary; it is left out of the
        // program and checked once the program is built (A31, A40).
        for (const b1 of allB) {
          for (const b2 of allB) {
            const m = pairMeet(b1, b2);
            if (m.kind === "overlap") {
              emit(m.meet, "+", consequent, each(L(b1, "+", antecedent), L(b2, "+", a)));
            } else if (m.kind === "ambiguous" && antecedent !== undefined) {
              ambiguousCuts.push({ b1, b2, antecedent, implication: a, reason: m.reason });
            }
          }
        }
        for (const b of allB) {
          // Counterexample: record (B, -, C), Live (B, +, A).
          emit(b, "-", a, each(R(b, "-", consequent), L(b, "+", antecedent)));
          // imposs-excl: (B, -, A) from Live (B, +, A → ⊥).
          if (item.consequent.kind === "bottom") {
            emit(b, "-", antecedent, each(L(b, "+", a)));
          }
        }
        break;
      }
      case "forall":
      case "exists": {
        const constraint = item.domainConstraint;
        const instances = bs.handlesOf(item.domain).map((h) => ({
          body: idx(substituteHandle(item.body, item.variable, h.id)),
          delta:
            constraint !== undefined
              ? idx(substituteHandle(constraint, item.variable, h.id))
              : undefined,
        }));
        // A13 as amended: enumeration needs CloseDomain(D) and D ≠ ⊥_B; a closure listed for
        // ⊥_B is accepted and grounds nothing (A24).
        const closed = closedDomains.has(item.domain) && item.domain !== BOT_BOUNDARY;
        for (const b of allB) {
          const plusDelta = (delta: number | undefined): Prem[] =>
            constraint !== undefined ? [L(b, "+", delta)] : [];
          if (item.kind === "forall") {
            for (const { body, delta } of instances) {
              // ∀E
              emit(b, "+", body, each(L(b, "+", a), ...plusDelta(delta)));
              // ∀ counterexample
              emit(b, "-", a, each(R(b, "-", body), ...plusDelta(delta)));
            }
            // ∀ generic (A13): vacuous on an empty Dom(D) of a closed D ≠ ⊥_B.
            if (closed) {
              emit(
                b,
                "+",
                a,
                instances.map(({ body, delta }) =>
                  constraint !== undefined
                    ? [[L(b, "-", delta)], [L(b, "+", body), L(b, "+", delta)]]
                    : [[L(b, "+", body)]],
                ),
              );
            }
          } else {
            for (const { body, delta } of instances) {
              // ∃I
              emit(b, "+", a, each(L(b, "+", body), ...plusDelta(delta)));
            }
            // ∃ exclusion (A12): per handle, record (B, -, A(w)) or Live (B, -, δ(w)).
            if (closed) {
              emit(
                b,
                "-",
                a,
                instances.map(({ body, delta }) =>
                  constraint !== undefined
                    ? [[R(b, "-", body)], [L(b, "-", delta)]]
                    : [[R(b, "-", body)]],
                ),
              );
            }
          }
        }
        break;
      }
      case "atom":
      case "bottom":
      case "equiv":
      case "refl":
      case "ref":
        break;
    }
  });

  // Incompatibility: A ⊥_B C in C_B, at every B' ⊑ B (A19).
  for (const c of incompatibilities) {
    const left = idx(c.left);
    const right = idx(c.right);
    for (const sub of subsOf[boundaryIndex(c.boundary, "incompatibility boundary")] ?? []) {
      emit(sub, "-", right, each(L(sub, "+", left)));
      emit(sub, "-", left, each(L(sub, "+", right)));
    }
  }

  // Congruence items: Structural reflexivity, ≈ symmetry and transitivity, Congruence.
  const equivsByLeft = new Map<string, { readonly item: Equiv; readonly a: number }[]>();
  for (const e of equivs) {
    const key = `${e.item.boundary}\u0000${e.item.left}`;
    const list = equivsByLeft.get(key) ?? [];
    list.push(e);
    equivsByLeft.set(key, list);
  }
  for (const { item, a } of equivs) {
    const d = item.boundary;
    // Structural: (B, +, t ≈_B t) for t ∈ Dom(B) (A9).
    const dIndex = bIndex.get(d);
    if (item.left === item.right && dIndex !== undefined && bs.isAdmissibleHandle(d, item.left)) {
      emit(dIndex, "+", a, []);
    }
    // ≈ symmetry
    const swapped = idx(equiv(d, item.right, item.left));
    for (const b of allB) {
      emit(b, "+", swapped, each(L(b, "+", a)));
    }
    // ≈ transitivity: t ≈_D u and u ≈_D v give t ≈_D v.
    for (const next of equivsByLeft.get(`${d}\u0000${item.right}`) ?? []) {
      const target = idx(equiv(d, item.left, next.item.right));
      for (const b of allB) {
        emit(b, "+", target, each(L(b, "+", a), L(b, "+", next.a)));
      }
    }
    // Congruence: (B, p, R') from Live (B, +, t ≈_D u), Live (B, p, R), where R' replaces one
    // occurrence of t in R by u, R a relational atom native to D, B ⊑ D (A6 as amended, A7).
    if (item.left === item.right) {
      continue;
    }
    const subs = subsOfAnyBoundary(d);
    for (const r of relAtoms) {
      if (!r.handles.has(item.left) || !bs.hasNativeRelation(d, r.item.relation)) {
        continue;
      }
      r.item.roles.forEach((role, position) => {
        if (role.handle !== item.left) {
          return;
        }
        const target = idx(
          atom(
            r.item.relation,
            r.item.roles.map((other, j) =>
              j === position ? { role: other.role, handle: item.right } : other,
            ),
          ),
        );
        for (const b of subs) {
          for (const p of POLARITIES) {
            emit(b, p, target, each(L(b, "+", a), L(b, p, r.a)));
          }
        }
      });
    }
  }

  // Cover-Gluing: (B, p, A) from Live (Bᵢ, p, A) for every cell, {Bᵢ} ▷ B other than {B}. A
  // minimal cover other than {B} never holds B itself (A36).
  for (const b of allB) {
    for (const cells of coversOf[b] ?? []) {
      if (cells.length === 1 && cells[0] === b) {
        continue;
      }
      for (let a = 0; a < nu; a++) {
        for (const p of POLARITIES) {
          emit(
            b,
            p,
            a,
            cells.map((c) => [[L(c, p, a)]]),
          );
        }
      }
    }
  }

  // ---------------------------------------------------------------- well-founded model
  const nClauses = heads.length;
  const occurrences: number[][] = Array.from({ length: atomCount }, () => []);
  bodies.forEach((body, c) => {
    for (const x of body) {
      occurrences[x]?.push(c);
    }
  });

  /** Least model of the program with each `not obs(B, A)` read against `assumedObs`. */
  const leastModel = (assumedObs: Uint8Array): Uint8Array => {
    const truth = new Uint8Array(atomCount);
    const remaining = new Int32Array(nClauses);
    const stack: number[] = [];
    const fire = (atomId: number): void => {
      if (truth[atomId] !== 1) {
        truth[atomId] = 1;
        stack.push(atomId);
      }
    };
    for (let c = 0; c < nClauses; c++) {
      const guard = guards[c] ?? -1;
      if (guard >= 0 && assumedObs[guard] === 1) {
        remaining[c] = -1; // `not obs` is false under the assumption: the clause is dropped
        continue;
      }
      const length = bodies[c]?.length ?? 0;
      remaining[c] = length;
      if (length === 0) {
        fire(heads[c] ?? -1);
      }
    }
    for (let x = stack.pop(); x !== undefined; x = stack.pop()) {
      for (const c of occurrences[x] ?? []) {
        const left = remaining[c] ?? 0;
        if (left > 0) {
          remaining[c] = left - 1;
          if (left === 1) {
            fire(heads[c] ?? -1);
          }
        }
      }
    }
    return truth;
  };

  /** Γ(J): the least model under J's obs atoms, extended with its coll and obs atoms. */
  const gamma = (assumedObs: Uint8Array): Interpretation => {
    const truth = leastModel(assumedObs);
    const coll = new Uint8Array(nS);
    for (let s = 0; s < nS; s++) {
      coll[s] = truth[recAtom("+", s)] === 1 && truth[recAtom("-", s)] === 1 ? 1 : 0;
    }
    // obs(B, A) ← coll(B', A) for every B' ⊑ B, B itself included (A18).
    const obs = new Uint8Array(nS);
    for (const b of allB) {
      for (const sub of subsOf[b] ?? []) {
        for (let a = 0; a < nu; a++) {
          if (coll[slot(sub, a)] === 1) {
            obs[slot(b, a)] = 1;
          }
        }
      }
    }
    return { truth, coll, obs };
  };

  const sameTruth = (x: Uint8Array, y: Uint8Array): boolean =>
    x.length === y.length && x.every((v, i) => v === y[i]);

  // Alternating fixpoint: under_{k+1} = Γ(Γ(under_k)) rises from ∅ to lfp(Γ²), the true
  // atoms; over = Γ(lfp(Γ²)) is the set of atoms that are true or undefined.
  let under: Interpretation = {
    truth: new Uint8Array(atomCount),
    coll: new Uint8Array(nS),
    obs: new Uint8Array(nS),
  };
  let over = gamma(under.obs);
  let rounds = 1;

  // A31, A40 (item 14, Role, as amended in e869e9b): a Scoped Cut instance over an ambiguous pair
  // needs the meet when its Live premises are true in the least model of the program read with
  // every obs atom false and with the instances over ambiguous pairs left out. Γ(∅) is that model:
  // the program built above holds no such instance, and under ∅ every `not obs` holds. Every atom
  // true or undefined in the well-founded model is true in Γ(∅), and adding instances whose bodies
  // fail there changes no least model, so an instance whose premises are not both true there can
  // never fire, and its meet decides nothing.
  for (const cut of ambiguousCuts) {
    const antecedentLive = over.truth[liveAtom("+", slot(cut.b1, cut.antecedent))] === 1;
    const implicationLive = over.truth[liveAtom("+", slot(cut.b2, cut.implication))] === 1;
    if (antecedentLive && implicationLive) {
      const b1 = boundaryName(cut.b1);
      const b2 = boundaryName(cut.b2);
      const premise = (b: string, a: number): string =>
        `Live (${b}, +, ${itemKey(universe[a] ?? bottom())})`;
      throw new Error(
        `Π(Σ) oracle: Scoped Cut from ${premise(b1, cut.antecedent)} and ${premise(b2, cut.implication)} needs the meet of "${b1}" and "${b2}", which is ambiguous (${cut.reason}).`,
      );
    }
  }
  for (;;) {
    const next = gamma(over.obs);
    rounds += 1;
    if (sameTruth(next.truth, under.truth)) {
      break;
    }
    under = next;
    over = gamma(under.obs);
    rounds += 1;
  }
  for (let x = 0; x < atomCount; x++) {
    if (under.truth[x] === 1 && over.truth[x] !== 1) {
      throw new Error("Π(Σ) oracle: internal error, a true atom is missing from Γ(true).");
    }
  }

  // ---------------------------------------------------------------- reporting
  const truthOf = (u: Uint8Array, o: Uint8Array, i: number): Truth =>
    u[i] === 1 ? "true" : o[i] === 1 ? "undefined" : "false";
  // A21: an absent record has no authority.
  const authorityOf = (present: boolean, live: Truth): Authority | null =>
    !present ? null : live === "true" ? "Live" : live === "undefined" ? "Undetermined" : "Quarantined";

  const rows: PiRow[] = [];
  const rowIndex = new Map<string, PiRow>();
  const revisionObligations: { boundary: string; item: Item }[] = [];
  for (const b of allB) {
    universe.forEach((item, a) => {
      const s = slot(b, a);
      const rec = {
        "+": truthOf(under.truth, over.truth, recAtom("+", s)),
        "-": truthOf(under.truth, over.truth, recAtom("-", s)),
      };
      const live = {
        "+": truthOf(under.truth, over.truth, liveAtom("+", s)),
        "-": truthOf(under.truth, over.truth, liveAtom("-", s)),
      };
      const coll = truthOf(under.coll, over.coll, s);
      // G4b: a record is present only when its atom is true, while Collision is reported
      // whenever coll is true or undefined.
      const present = { "+": rec["+"] === "true", "-": rec["-"] === "true" };
      const localStatus: LocalStatus =
        coll !== "false"
          ? "Collision"
          : present["+"]
            ? "Grounded"
            : present["-"]
              ? "Excluded"
              : "Open";
      const revisionObligation = coll !== "false";
      const row: PiRow = {
        boundary: boundaryName(b),
        item,
        rec,
        live,
        coll,
        obs: truthOf(under.obs, over.obs, s),
        present,
        localStatus,
        authority: {
          "+": authorityOf(present["+"], live["+"]),
          "-": authorityOf(present["-"], live["-"]),
        },
        revisionObligation,
      };
      rows.push(row);
      rowIndex.set(`${boundaryName(b)}\u0000${itemKey(item)}`, row);
      if (revisionObligation) {
        revisionObligations.push({ boundary: boundaryName(b), item });
      }
    });
  }

  // OverlapUnknown (A28–A31): for each unordered pair of distinct boundaries whose overlap is
  // unknown, every item with a present +A record on one and a present -A record on the other.
  // Presence is G4b's (rec true); authority and the record's origin do not matter.
  const isPresent = (b: number, p: Polarity, a: number): boolean =>
    under.truth[recAtom(p, slot(b, a))] === 1;
  const overlapObligations: PiOverlapObligation[] = [];
  for (let left = 0; left < nb; left++) {
    for (let right = left + 1; right < nb; right++) {
      let kind: PairMeet["kind"] | undefined;
      for (const [a, item] of universe.entries()) {
        const opposed =
          (isPresent(left, "+", a) && isPresent(right, "-", a)) ||
          (isPresent(left, "-", a) && isPresent(right, "+", a));
        if (!opposed) {
          continue;
        }
        kind ??= neededMeet(left, right, "reporting OverlapUnknown").kind;
        if (kind !== "unknown") {
          break;
        }
        overlapObligations.push({ left: boundaryName(left), right: boundaryName(right), item });
      }
    }
  }

  return {
    boundaries,
    universe,
    rows,
    revisionObligations,
    overlapObligations,
    witnessedCovers,
    coverObligations,
    rounds,
    at(boundary: string, item: Item): PiRow {
      const row = rowIndex.get(`${boundary}\u0000${itemKey(item)}`);
      if (row === undefined) {
        throw new Error(
          `Π(Σ) oracle: (${boundary}, ${itemKey(item)}) is outside 𝔅(Σ) × U(Σ, Q).`,
        );
      }
      return row;
    },
  };
}
