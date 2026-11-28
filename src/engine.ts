/**
 * Dual-polarity semantics, Inference Quarantine, Scoped Cut, vertical inquiry
 * transitions (Observe/Retract/RefineBoundary/Constrain/WitnessCover/CloseDomain),
 * and M1/M2 anti-immunization laws for UL-Core.
 *
 * Implements spec/core.md §2 item 7 and §3 items 8-12 as a projection of the
 * evaluation program Π(Σ) of §5 item 14: ground records, collisions, obstruction
 * and transmission authority are read from the well-founded model of Π(Σ)
 * (Van Gelder, Ross and Schlipf, 1991), computed by the alternating fixpoint.
 * Provenance entries are finite derivations that witness the true atoms of that
 * model; they explain records and never decide them.
 */

import { BOT_BOUNDARY, BoundarySystem, type MeetStatus } from "./boundary.ts";
import {
  and,
  atom,
  bottom,
  collectBoundaryRefs,
  collectHandles,
  collectRelations,
  computeItemLevel,
  equiv,
  implies,
  itemKey,
  or,
  substituteHandle,
  type Item,
  type Polarity,
} from "./syntax.ts";

export type LocalStatus = "Open" | "Grounded" | "Excluded" | "Collision";

/** Authority of a present record (spec/core.md §5 item 14, Reporting). */
export type Authority = "Live" | "Undetermined" | "Quarantined";

type StructuralRule = "bottom-excl" | "struct-imposs" | "refl-eval" | "equiv-refl";

export type Provenance =
  | { readonly kind: "base"; readonly baseId: string }
  | { readonly kind: "structural"; readonly rule: StructuralRule }
  | {
      readonly kind: "derived";
      readonly rule: string;
      readonly depEntryIds: readonly string[];
      readonly baseLeaves: readonly string[];
      readonly coverCells?: readonly string[];
    };

export type GroundEntry = {
  readonly entryId: string;
  readonly boundary: string;
  readonly polarity: Polarity;
  readonly item: Item;
  readonly key: string;
  readonly provenance: Provenance;
};

export type HandleAuth = {
  readonly handle: string;
  readonly criterion: string;
};

/** A registered incompatibility A ⊥_B C, with the identifier Withdraw names it by. */
export type IncompatibilityConstraint = {
  readonly id: string;
  readonly boundary: string;
  readonly left: Item;
  readonly right: Item;
};

export type M1RefinementRequest = {
  readonly fromBoundary: string;
  readonly toBoundary: string;
  readonly originalUniversal: Item;
  readonly targetRelation: string;
  readonly criterionItem: Item;
  readonly criterionVariable?: string;
};

export type M1Result =
  | {
      readonly ok: true;
      readonly fromBoundary: string;
      readonly toBoundary: string;
      readonly originalStatusBefore: LocalStatus;
      readonly originalExcludedPreserved: boolean;
    }
  | {
      readonly ok: false;
      readonly violation:
        | "M1-circular"
        | "M1-contingent-excision"
        | "M1-unwitnessed-proxy"
        | "M1-unbound-criterion"
        | "M1-target-absent"
        | "M1-empty-excision"
        | "M2-not-refuted";
      readonly reason: string;
    };

/**
 * OverlapUnknown(B₁, B₂, A) (core.md §5 item 14): `A` has a present `+` record on one of two boundaries
 * and a present `-` record on the other, and nothing registered settles whether they overlap.
 */
export type OverlapObligation = {
  readonly left: string;
  readonly right: string;
  readonly itemKey: string;
};

/** The kinds of constraint in C_B that Withdraw removes (core.md §2 item 7). */
export type ConstraintKind = "incompatibility" | "collapse" | "cover" | "closure";

/**
 * A revision obligation against a registered cover that is not valid (core.md §2 item 5): invalid
 * when some witness B' ⊑ B is disjoint from every cell, unverified when a witness is known to
 * overlap no cell and has an unknown overlap with some cell.
 */
export type CoverObligation = {
  readonly coverId: string;
  readonly target: string;
  readonly cells: readonly string[];
  readonly validity: "invalid" | "unverified";
  readonly witnesses: readonly string[];
};

/** The obligations an evaluation reports besides Rev(B, A). */
type SnapshotObligations = {
  readonly refinement?: readonly RefinementObligation[];
  readonly overlap?: readonly OverlapObligation[];
  readonly cover?: readonly CoverObligation[];
};

/** An admitted RefineBoundary transition, kept in Σ so later evidence can be checked against it. */
export type RecordedRefinement = {
  readonly fromBoundary: string;
  readonly toBoundary: string;
  readonly criterionItem: Item;
  readonly criterionVariable: string;
};

/**
 * A revision obligation against an admitted refinement (core.md §2 item 7, M1): a handle kept in
 * the refined boundary now carries `Live -δ(handle)` on the original boundary.
 */
export type RefinementObligation = {
  readonly fromBoundary: string;
  readonly toBoundary: string;
  readonly handle: string;
  readonly criterionKey: string;
};

/** A cover a recorded theorem's derivation uses: the theorem holds only while it is witnessed. */
export type CoverDependency = {
  readonly boundary: string;
  readonly cells: readonly string[];
};

export type GroundDependency = {
  readonly boundary: string;
  readonly polarity: Polarity;
  readonly item: Item;
};

export type RevisionObligation = {
  readonly boundary: string;
  readonly itemKey: string;
};

export type EngineOptions = {
  readonly monotoneOnly?: boolean;
};

/**
 * Verify well-foundedness (acyclicity) of an explicit provenance adjacency graph.
 * Cycles grant zero grounding per spec/core.md §3 item 8.
 */
export function isWellFoundedGraph(
  adjacency: ReadonlyMap<string, readonly string[]>,
  activeLeaves: ReadonlySet<string>,
  startNode: string,
): boolean {
  const visiting = new Set<string>();
  const verified = new Set<string>();

  function dfs(node: string): boolean {
    if (verified.has(node)) {
      return true;
    }
    if (visiting.has(node)) {
      return false;
    }
    const deps = adjacency.get(node);
    if (deps === undefined || deps.length === 0) {
      return activeLeaves.has(node);
    }
    visiting.add(node);
    for (const dep of deps) {
      if (!dfs(dep)) {
        return false;
      }
    }
    visiting.delete(node);
    verified.add(node);
    return true;
  }

  return dfs(startNode);
}

/** Truth codes stored per slot: 0 = false, 1 = undefined, 2 = true. */
const FALSE = 0;
const UNDEFINED = 1;
const TRUE = 2;

/** Polarity index used in flat slot arrays. */
function polIndex(p: Polarity): 0 | 1 {
  return p === "+" ? 0 : 1;
}

/** The well-founded model of Π(Σ) over 𝔅(Σ) × U(Σ, Q), with its witnessing entries. */
type PiReport = {
  readonly boundaries: readonly string[];
  readonly universe: readonly Item[];
  /** rec(B, p, A) per polarity index, one code per slot (b * |U| + a). */
  readonly rec: readonly [Uint8Array, Uint8Array];
  /** live(B, p, A) per polarity index. */
  readonly live: readonly [Uint8Array, Uint8Array];
  readonly coll: Uint8Array;
  readonly obs: Uint8Array;
  readonly entries: readonly GroundEntry[];
  readonly liveEntryIds: ReadonlySet<string>;
};

/**
 * Snapshot of the well-founded model of Π(Σ) (spec/core.md §5 item 14) at the current Σ
 * and query set Q. Slots outside 𝔅(Σ) × U(Σ, Q) have no atoms: they read as `Open`, with
 * no records and no authority.
 */
export class EvaluationSnapshot {
  readonly #boundaries: readonly string[];
  readonly #boundaryIndex: ReadonlyMap<string, number>;
  readonly #universe: readonly Item[];
  readonly #itemIndex: ReadonlyMap<string, number>;
  readonly #rec: readonly [Uint8Array, Uint8Array];
  readonly #live: readonly [Uint8Array, Uint8Array];
  readonly #coll: Uint8Array;
  readonly #obs: Uint8Array;
  readonly #entriesById = new Map<string, GroundEntry>();
  readonly #bySlot = new Map<number, GroundEntry[]>();
  readonly #liveIds: ReadonlySet<string>;
  readonly #refinementObligations: readonly RefinementObligation[];
  readonly #overlapObligations: readonly OverlapObligation[];
  readonly #coverObligations: readonly CoverObligation[];

  constructor(report: PiReport, obligations: SnapshotObligations = {}) {
    this.#refinementObligations = obligations.refinement ?? [];
    this.#overlapObligations = obligations.overlap ?? [];
    this.#coverObligations = obligations.cover ?? [];
    this.#boundaries = report.boundaries;
    this.#boundaryIndex = new Map(report.boundaries.map((b, i) => [b, i] as const));
    this.#universe = report.universe;
    this.#itemIndex = new Map(report.universe.map((it, i) => [itemKey(it), i] as const));
    this.#rec = report.rec;
    this.#live = report.live;
    this.#coll = report.coll;
    this.#obs = report.obs;
    this.#liveIds = report.liveEntryIds;
    for (const e of report.entries) {
      this.#entriesById.set(e.entryId, e);
      const s = this.#slot(e.boundary, e.item);
      if (s === undefined) {
        continue;
      }
      const k = s * 2 + polIndex(e.polarity);
      const list = this.#bySlot.get(k) ?? [];
      list.push(e);
      this.#bySlot.set(k, list);
    }
  }

  #slot(boundary: string, item: Item): number | undefined {
    const b = this.#boundaryIndex.get(boundary);
    if (b === undefined) {
      return undefined;
    }
    const a = this.#itemIndex.get(itemKey(item));
    if (a === undefined) {
      return undefined;
    }
    return b * this.#universe.length + a;
  }

  /** U(Σ, Q): the items that carry atoms in this snapshot. */
  universe(): readonly Item[] {
    return this.#universe;
  }

  /**
   * Local status of (boundary, item) under item 14: `Collision` when coll(B, A) is true or
   * undefined; otherwise `Grounded`, `Excluded` or `Open` by its present (true) records.
   */
  localStatus(boundary: string, item: Item): LocalStatus {
    const s = this.#slot(boundary, item);
    if (s === undefined) {
      return "Open";
    }
    if (this.#coll[s] !== FALSE) {
      return "Collision";
    }
    if (this.#rec[0][s] === TRUE) {
      return "Grounded";
    }
    if (this.#rec[1][s] === TRUE) {
      return "Excluded";
    }
    return "Open";
  }

  /**
   * Authority of the record (boundary, polarity, item): `Live` when live(B, p, A) is true,
   * `Undetermined` when it is undefined, `Quarantined` when it is false; null when the record
   * is absent (its rec atom is not true).
   */
  authorityOf(boundary: string, polarity: Polarity, item: Item): Authority | null {
    const s = this.#slot(boundary, item);
    const pi = polIndex(polarity);
    if (s === undefined || this.#rec[pi][s] !== TRUE) {
      return null;
    }
    const live = this.#live[pi][s];
    return live === TRUE ? "Live" : live === UNDEFINED ? "Undetermined" : "Quarantined";
  }

  /** Witnessing entries of a present record (Live or not) for (boundary, polarity, item). */
  allGrounds(boundary: string, polarity: Polarity, item: Item): readonly GroundEntry[] {
    const s = this.#slot(boundary, item);
    if (s === undefined) {
      return [];
    }
    return this.#bySlot.get(s * 2 + polIndex(polarity)) ?? [];
  }

  /** Witnessing entries whose premises are all Live on an unobstructed slot. */
  liveGrounds(boundary: string, polarity: Polarity, item: Item): readonly GroundEntry[] {
    return this.allGrounds(boundary, polarity, item).filter((e) => this.#liveIds.has(e.entryId));
  }

  /** True iff the authority of (boundary, polarity, item) is `Live`. */
  isLive(boundary: string, polarity: Polarity, item: Item): boolean {
    const s = this.#slot(boundary, item);
    return s !== undefined && this.#live[polIndex(polarity)][s] === TRUE;
  }

  /** Return true iff a specific entryId is a Live derivation. */
  isEntryLive(entryId: string): boolean {
    return this.#liveIds.has(entryId);
  }

  /** True iff (boundary, item) is in Collision (coll true or undefined). */
  isCollided(boundary: string, item: Item): boolean {
    const s = this.#slot(boundary, item);
    return s !== undefined && this.#coll[s] !== FALSE;
  }

  /**
   * True iff (boundary, item) is obstructed: obs(B, A) is true or undefined, that is, some
   * sub-boundary B' ⊑ B (B itself included) is in Collision.
   */
  isObstructed(boundary: string, item: Item): boolean {
    const s = this.#slot(boundary, item);
    return s !== undefined && this.#obs[s] !== FALSE;
  }

  /** Rev(B, A) for every (B, A) in Collision. */
  revisionObligations(): readonly RevisionObligation[] {
    const out: RevisionObligation[] = [];
    const nu = this.#universe.length;
    this.#boundaries.forEach((boundary, b) => {
      this.#universe.forEach((item, a) => {
        if (this.#coll[b * nu + a] !== FALSE) {
          out.push({ boundary, itemKey: itemKey(item) });
        }
      });
    });
    return out;
  }

  /**
   * Revision obligations against admitted refinements: each handle kept in a refined boundary
   * that now carries `Live -δ(handle)` on the original boundary (core.md §2 item 7, M1).
   */
  refinementObligations(): readonly RefinementObligation[] {
    return this.#refinementObligations;
  }

  /**
   * OverlapUnknown obligations (core.md §5 item 14): opposite present records of an item on two
   * boundaries whose overlap is unknown.
   */
  overlapObligations(): readonly OverlapObligation[] {
    return this.#overlapObligations;
  }

  /** Revision obligations against registered covers that are invalid or unverified (item 5). */
  coverObligations(): readonly CoverObligation[] {
    return this.#coverObligations;
  }

  /** True iff a record of (boundary, polarity, item) is present: its rec atom is true. */
  hasRecord(boundary: string, polarity: Polarity, item: Item): boolean {
    const s = this.#slot(boundary, item);
    return s !== undefined && this.#rec[polIndex(polarity)][s] === TRUE;
  }

  /** True iff No-Gluts holds: no (B, A) is in Collision. */
  isCollisionFree(): boolean {
    return this.#coll.every((c) => c === FALSE);
  }

  /** Retrieve an entry by ID. */
  entryById(entryId: string): GroundEntry | undefined {
    return this.#entriesById.get(entryId);
  }
}

type BaseObservation = {
  readonly baseId: string;
  readonly boundary: string;
  readonly polarity: Polarity;
  readonly item: Item;
  readonly key: string;
};

type RecordedTheorem = {
  readonly theoremId: string;
  readonly boundary: string;
  readonly polarity: Polarity;
  readonly item: Item;
  readonly requiredBaseIds: readonly string[];
  readonly requiredGrounds: readonly GroundDependency[];
  readonly requiredCovers: readonly CoverDependency[];
};

type StructuralCollapse = { readonly id: string; readonly boundary: string; readonly item: Item };

type StageRecord = {
  readonly stage: number;
  readonly baseObservations: ReadonlyMap<string, BaseObservation>;
  readonly theorems: ReadonlyMap<string, RecordedTheorem>;
  readonly incompatibilities: readonly IncompatibilityConstraint[];
  readonly structuralCollapses: readonly StructuralCollapse[];
  readonly closedDomains: ReadonlySet<string>;
  readonly refinements: readonly RecordedRefinement[];
  /** The items tracked by Σ: ⊥ and every item named by a transition so far, retracted ones included. */
  readonly trackedItems: ReadonlyMap<string, Item>;
  readonly boundarySnapshot: BoundarySystem;
};

/**
 * Stateful vertical inquiry engine managing Σ = (G+, G-, C_B, O_rev) and
 * evaluating Π(Σ) for the current or an archived stage.
 */
export class InquiryEngine {
  readonly boundaries: BoundarySystem;
  readonly monotoneOnly: boolean;
  readonly #baseObservations = new Map<string, BaseObservation>();
  readonly #theorems = new Map<string, RecordedTheorem>();
  readonly #incompatibilities: IncompatibilityConstraint[] = [];
  readonly #structuralCollapses: StructuralCollapse[] = [];
  /**
   * CloseDomain closures in C_B: constraint identifier to the domain and the handle set of Dom(D)
   * the closure witnessed. A closure gates enumeration only while Dom(D) equals that set.
   */
  readonly #closures = new Map<string, { readonly domain: string; readonly handles: string }>();
  /** Every constraint of C_B in force, by identifier. */
  readonly #constraintKinds = new Map<string, ConstraintKind>();
  /** Identifiers ever given to a constraint; Withdraw does not free them for reuse. */
  readonly #usedConstraintIds = new Set<string>();
  /** Identifiers ever given to a base observation or a theorem; Retract does not free them. */
  readonly #usedBaseIds = new Set<string>();
  readonly #usedTheoremIds = new Set<string>();
  #constraintCounter = 0;
  /** The boundary-system version the current stage captured. */
  #boundaryVersion = -1;
  readonly #refinements: RecordedRefinement[] = [];
  readonly #trackedItems = new Map<string, Item>();
  readonly #stageArchive = new Map<number, StageRecord>();
  readonly #history: string[] = [];
  #stage = 0;

  constructor(boundaries: BoundarySystem, options: EngineOptions = {}) {
    this.boundaries = boundaries;
    this.monotoneOnly = options.monotoneOnly ?? false;
    this.#track(bottom());
    this.#captureStage();
  }

  get stage(): number {
    this.#syncBoundaries();
    return this.#stage;
  }

  get transitionLog(): readonly string[] {
    this.#syncBoundaries();
    return this.#history;
  }

  /**
   * Declare (core.md §2 item 7): a change of the boundary system made outside an inquiry transition
   * becomes a stage of its own before the next transition or evaluation, so evaluate() and
   * evaluateAtStage at the current stage agree. A cover registered directly on the boundary system
   * becomes a constraint that Withdraw can name; one withdrawn there leaves the constraints.
   */
  #syncBoundaries(): void {
    if (this.boundaries.version === this.#boundaryVersion) {
      return;
    }
    const registered = new Set(this.boundaries.registeredCovers().map((c) => c.id));
    for (const id of registered) {
      if (!this.#constraintKinds.has(id)) {
        if (this.#usedConstraintIds.has(id)) {
          throw new Error(`The cover "${id}" registered on the boundary system reuses a constraint identifier of this inquiry.`);
        }
        this.#recordConstraintId(id, "cover");
      }
    }
    for (const [id, kind] of this.#constraintKinds) {
      if (kind === "cover" && !registered.has(id)) {
        this.#constraintKinds.delete(id);
      }
    }
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Declare(boundaries)`);
    this.#captureStage();
  }

  /** Add a base positive witness G+ on non-empty boundary B != ⊥_B. */
  observePositive(
    boundary: string,
    item: Item,
    baseId: string,
    handleAuth?: HandleAuth,
  ): void {
    if (boundary === BOT_BOUNDARY) {
      throw new Error(
        `Non-Witnessing Law violation: impossible boundary "${BOT_BOUNDARY}" cannot supply a positive witness.`,
      );
    }
    if (item.kind === "bottom") {
      throw new Error(
        `Unsatisfiable item "⊥" admits no positive witness on non-empty boundary "${boundary}".`,
      );
    }
    this.#addBaseObservation(boundary, "+", item, baseId, handleAuth);
  }

  /** Add a base negative exclusion G- on non-empty boundary B != ⊥_B. */
  observeNegative(
    boundary: string,
    item: Item,
    baseId: string,
    handleAuth?: HandleAuth,
  ): void {
    if (boundary === BOT_BOUNDARY) {
      throw new Error(`Cannot record base observation on "${BOT_BOUNDARY}".`);
    }
    this.#addBaseObservation(boundary, "-", item, baseId, handleAuth);
  }

  /**
   * Record an externally verified natural-deduction theorem back into Σ
   * anchored to any underlying base leaf IDs so Quarantine and Retract propagate cleanly.
   */
  recordTheorem(
    boundary: string,
    polarity: Polarity,
    item: Item,
    theoremId: string,
    requiredBaseIds: readonly string[] = [],
    requiredGrounds: readonly GroundDependency[] = [],
    requiredCovers: readonly CoverDependency[] = [],
  ): void {
    this.#syncBoundaries();
    if (boundary === BOT_BOUNDARY) {
      throw new Error(
        polarity === "+"
          ? `Non-Witnessing Law violation: impossible boundary "${BOT_BOUNDARY}" cannot supply a positive theorem.`
          : `Cannot record theorem on "${BOT_BOUNDARY}".`,
      );
    }
    if (polarity === "+" && item.kind === "bottom") {
      throw new Error(
        `Unsatisfiable item "⊥" admits no positive witness on non-empty boundary "${boundary}".`,
      );
    }
    this.boundaries.nonEmptySubBoundaries(boundary);
    if (this.#usedTheoremIds.has(theoremId)) {
      throw new Error(`Theorem identifier "${theoremId}" is already used in this inquiry.`);
    }
    this.#usedTheoremIds.add(theoremId);
    this.#track(item);
    for (const dep of requiredGrounds) {
      this.#track(dep.item);
    }
    this.#theorems.set(theoremId, {
      theoremId,
      boundary,
      polarity,
      item,
      requiredBaseIds: [...requiredBaseIds],
      requiredGrounds: [...requiredGrounds],
      requiredCovers: requiredCovers.map((c) => ({ boundary: c.boundary, cells: [...c.cells] })),
    });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Theorem${polarity}(${boundary}, ${itemKey(item)}, ${theoremId})`);
    this.#captureStage();
  }

  /**
   * Collect every handle identifier mentioned anywhere in Σ or registered boundaries, including
   * those named only by items Σ still tracks: retracted observations, withdrawn constraints and
   * refinements (core.md §5 item 14).
   */
  mentionedHandles(): ReadonlySet<string> {
    const out = new Set<string>();
    for (const item of this.#trackedItems.values()) {
      for (const h of collectHandles(item)) {
        out.add(h);
      }
    }
    for (const obs of this.#baseObservations.values()) {
      for (const h of collectHandles(obs.item)) {
        out.add(h);
      }
    }
    for (const thm of this.#theorems.values()) {
      for (const h of collectHandles(thm.item)) {
        out.add(h);
      }
    }
    for (const inc of this.#incompatibilities) {
      for (const h of collectHandles(inc.left)) {
        out.add(h);
      }
      for (const h of collectHandles(inc.right)) {
        out.add(h);
      }
    }
    for (const sc of this.#structuralCollapses) {
      for (const h of collectHandles(sc.item)) {
        out.add(h);
      }
    }
    for (const b of this.boundaries.nonEmptyBoundaries()) {
      for (const h of this.boundaries.handlesOf(b)) {
        out.add(h.id);
      }
    }
    return out;
  }

  /**
   * Pure Cancellation / Retraction (Sanskrit prasajya-pratisedha):
   * remove a specific base leaf without creating any opposite polarity.
   */
  retract(baseId: string): boolean {
    this.#syncBoundaries();
    if (this.monotoneOnly) {
      throw new Error("Retract is forbidden when monotoneOnly is enabled.");
    }
    const deleted = this.#baseObservations.delete(baseId);
    if (deleted) {
      this.#stage += 1;
      this.#history.push(`Σ${this.#stage}:Retract(${baseId})`);
      this.#captureStage();
    }
    return deleted;
  }

  /**
   * Register material incompatibility constraint A ⊥_B C in C_B under `constraintId` (a fresh one
   * when omitted), and return the identifier.
   */
  addIncompatibility(boundary: string, left: Item, right: Item, constraintId?: string): string {
    this.#syncBoundaries();
    if (boundary === BOT_BOUNDARY) {
      throw new Error(`Cannot add material incompatibility on "${BOT_BOUNDARY}".`);
    }
    this.boundaries.nonEmptySubBoundaries(boundary);
    const id = this.#claimConstraintId(constraintId, "incompatibility");
    this.#track(left);
    this.#track(right);
    this.#incompatibilities.push({ id, boundary, left, right });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Constrain(${itemKey(left)} ⊥_${boundary} ${itemKey(right)})`);
    this.#captureStage();
    return id;
  }

  /**
   * Register structural boundary collapse B ⊓ [A] = ⊥_B, inducing +(A → ⊥) and -A, under
   * `constraintId` (a fresh one when omitted), and return the identifier.
   */
  addStructuralCollapse(boundary: string, item: Item, constraintId?: string): string {
    this.#syncBoundaries();
    if (boundary === BOT_BOUNDARY) {
      throw new Error(`Cannot add structural collapse on "${BOT_BOUNDARY}".`);
    }
    this.boundaries.nonEmptySubBoundaries(boundary);
    const id = this.#claimConstraintId(constraintId, "collapse");
    this.#track(item);
    this.#track(implies(item, bottom()));
    this.#structuralCollapses.push({ id, boundary, item });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Collapse(${boundary} ⊓ [${itemKey(item)}] = ⊥_B)`);
    this.#captureStage();
    return id;
  }

  /**
   * Register a witnessed finite exhaustive cover {B_i} ▷ B as an ordered inquiry transition under
   * `constraintId` (a fresh one when omitted), and return the identifier. Later boundary changes
   * may make the cover invalid or unverified (core.md §2 item 5); coverObligations reports it.
   */
  witnessCover(target: string, cells: readonly string[], constraintId?: string): string {
    this.#syncBoundaries();
    const id = this.#nextConstraintId(constraintId);
    this.boundaries.registerCover(target, cells, id);
    this.#recordConstraintId(id, "cover");
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:WitnessCover({${cells.join(", ")}} ▷ ${target})`);
    this.#captureStage();
    return id;
  }

  /**
   * CloseDomain(D) (spec/core.md §2 item 7): register in C_B, for a boundary D ≠ ⊥_B, that the
   * handles of Dom(D) exhaust D. Only a closed domain licenses the enumerative rules `∀`
   * generic and `∃` exclusion of item 14; the closure applies to D itself, never to its
   * sub-boundaries.
   */
  closeDomain(domain: string, constraintId?: string): string {
    this.#syncBoundaries();
    if (domain === BOT_BOUNDARY) {
      throw new Error(`CloseDomain requires a boundary D ≠ "${BOT_BOUNDARY}".`);
    }
    const handles = handleSignature(this.boundaries, domain);
    const id = this.#claimConstraintId(constraintId, "closure");
    this.#closures.set(id, { domain, handles });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:CloseDomain(${domain})`);
    this.#captureStage();
    return id;
  }

  /**
   * True iff a closure of domain is in force at the current stage: registered in C_B and still
   * witnessing Dom(domain), which only a Declare that widens Dom(⊤_B) changes (core.md §2 item 7).
   */
  isDomainClosed(domain: string): boolean {
    this.#syncBoundaries();
    return this.#closedDomains(this.boundaries).has(domain);
  }

  /** The domains whose closure in C_B witnesses their current handle set in `bounds`. */
  #closedDomains(bounds: BoundarySystem): Set<string> {
    return new Set(
      [...this.#closures.values()]
        .filter((c) => c.handles === handleSignature(bounds, c.domain))
        .map((c) => c.domain),
    );
  }

  /** The incompatibilities A ⊥_B C in force in C_B. */
  incompatibilitiesInForce(): readonly IncompatibilityConstraint[] {
    return [...this.#incompatibilities];
  }

  /** The structural collapses B ⊓ [A] = ⊥_B in force in C_B. */
  collapsesInForce(): readonly { readonly id: string; readonly boundary: string; readonly item: Item }[] {
    return [...this.#structuralCollapses];
  }

  /** The kind of the constraint `constraintId` in force in C_B, or undefined. */
  constraintKind(constraintId: string): ConstraintKind | undefined {
    this.#syncBoundaries();
    return this.#constraintKinds.get(constraintId);
  }

  /**
   * Withdraw(c) (Pure Cancellation, core.md §2 item 7): remove the constraint `constraintId` (an
   * incompatibility, structural collapse, cover or closure) from C_B without adding anything to
   * Σ. The items it named stay tracked. Returns false when no such constraint is in force.
   */
  withdraw(constraintId: string): boolean {
    this.#syncBoundaries();
    if (this.monotoneOnly) {
      throw new Error("Withdraw is forbidden when monotoneOnly is enabled.");
    }
    const kind = this.#constraintKinds.get(constraintId);
    if (kind === undefined) {
      return false;
    }
    switch (kind) {
      case "incompatibility": {
        const i = this.#incompatibilities.findIndex((c) => c.id === constraintId);
        this.#incompatibilities.splice(i, 1);
        break;
      }
      case "collapse": {
        const i = this.#structuralCollapses.findIndex((c) => c.id === constraintId);
        this.#structuralCollapses.splice(i, 1);
        break;
      }
      case "closure":
        this.#closures.delete(constraintId);
        break;
      case "cover":
        this.boundaries.withdrawCover(constraintId);
        break;
    }
    this.#constraintKinds.delete(constraintId);
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Withdraw(${constraintId})`);
    this.#captureStage();
    return true;
  }

  /** The identifier for a new constraint: `requested`, refused if ever used, or a fresh one. */
  #nextConstraintId(requested: string | undefined): string {
    if (requested !== undefined) {
      if (this.#usedConstraintIds.has(requested)) {
        throw new Error(`Constraint identifier "${requested}" is already used in this inquiry.`);
      }
      return requested;
    }
    let id: string;
    do {
      this.#constraintCounter += 1;
      id = `c${this.#constraintCounter}`;
    } while (this.#usedConstraintIds.has(id));
    return id;
  }

  #recordConstraintId(id: string, kind: ConstraintKind): void {
    this.#usedConstraintIds.add(id);
    this.#constraintKinds.set(id, kind);
  }

  #claimConstraintId(requested: string | undefined, kind: ConstraintKind): string {
    const id = this.#nextConstraintId(requested);
    this.#recordConstraintId(id, kind);
    return id;
  }

  /** Verify that targetBoundary and all boundaries referenced inside targetItem existed as non-empty at `stage`. */
  isReflectionWellScopedAtStage(
    stage: number,
    targetBoundary: string,
    targetItem: Item,
  ): boolean {
    if (!Number.isInteger(stage) || stage < 0 || stage > this.#stage) {
      return false;
    }
    const priorRecord = this.#stageArchive.get(stage);
    if (priorRecord === undefined) {
      return false;
    }
    const priorBounds = priorRecord.boundarySnapshot;
    if (!this.#isDefinedNonEmptyBoundary(priorBounds, targetBoundary)) {
      return false;
    }
    for (const bRef of collectBoundaryRefs(targetItem)) {
      if (!this.#isDefinedNonEmptyBoundary(priorBounds, bRef)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Attempt RefineBoundary(fromBoundary -> toBoundary) obeying M1 + M2.
   * Rejects circular predicates (M1(i)) and bare contingent handle excisions (M1(ii)),
   * and verifies that M2 preserves Excluded (-) on (fromBoundary, originalUniversal).
   */
  refineBoundary(req: M1RefinementRequest): M1Result {
    this.#syncBoundaries();
    if (
      req.toBoundary === BOT_BOUNDARY ||
      !this.boundaries.refines(req.toBoundary, req.fromBoundary)
    ) {
      throw new Error(
        `Invalid refinement: "${req.toBoundary}" must be a non-empty sub-boundary of "${req.fromBoundary}".`,
      );
    }

    // The request must name a relation of the universal, and the refinement must excise a handle:
    // RefineBoundary narrows the regime past a counterexample (core.md §2 item 7).
    if (!collectRelations(req.originalUniversal).has(req.targetRelation)) {
      return {
        ok: false,
        violation: "M1-target-absent",
        reason: `The target relation "${req.targetRelation}" does not occur in the universal ${itemKey(req.originalUniversal)}.`,
      };
    }
    const keptHandles = new Set(this.boundaries.handlesOf(req.toBoundary).map((h) => h.id));
    if (this.boundaries.handlesOf(req.fromBoundary).every((h) => keptHandles.has(h.id))) {
      return {
        ok: false,
        violation: "M1-empty-excision",
        reason: `RefineBoundary(${req.fromBoundary} → ${req.toBoundary}) excises no handle of Dom(${req.fromBoundary}).`,
      };
    }

    const beforeSnap = this.evaluate([req.originalUniversal]);
    const statusBefore = beforeSnap.localStatus(req.fromBoundary, req.originalUniversal);
    if (statusBefore !== "Excluded" && statusBefore !== "Collision") {
      return {
        ok: false,
        violation: "M2-not-refuted",
        reason: `Original claim on "${req.fromBoundary}" is "${statusBefore}", not refuted.`,
      };
    }

    // M1(i) Non-Circularity: δ cannot reference targetRelation.
    const criterionRels = collectRelations(req.criterionItem);
    if (criterionRels.has(req.targetRelation)) {
      return {
        ok: false,
        violation: "M1-circular",
        reason: `M1(i) Non-Circularity violation: splitting criterion references target relation "${req.targetRelation}".`,
      };
    }

    // M1(i), indirect reference: δ's relations must not reach the target relation through the
    // relation-dependency graph of C_B (incompatibilities, structural collapses) and the Live
    // conditionals of Σ.
    const link = this.#indirectLink(req.criterionItem, req.targetRelation, req.fromBoundary, beforeSnap);
    if (link !== undefined) {
      return {
        ok: false,
        violation: "M1-circular",
        reason: `M1(i) Non-Circularity violation: splitting criterion relation "${link}" is linked to target relation "${req.targetRelation}" through registered constraints or Live conditionals.`,
      };
    }

    // M1(ii) Non-Contingent Structural Definability: δ cannot excise contingent handle tags.
    const criterionHandles = collectHandles(req.criterionItem);
    for (const h of criterionHandles) {
      const spec = this.boundaries.getHandle(req.fromBoundary, h);
      if (spec !== undefined && spec.kind === "contingent") {
        return {
          ok: false,
          violation: "M1-contingent-excision",
          reason: `M1(ii) violation: splitting criterion excises contingent handle "${h}".`,
        };
      }
    }

    // M1(iii) Independent Excess-Content Witness (Anti-Proxy Guard):
    // When contingent handles are excised, reject vacuous sub-boundaries and require at least one
    // non-refuted surviving handle u in toBoundary where δ(u) carries a Live (+) witness
    // (and no surviving handle witnesses Live (-)).
    const fromHandles = this.boundaries.handlesOf(req.fromBoundary);
    const toHandleIds = new Set(this.boundaries.handlesOf(req.toBoundary).map((h) => h.id));
    const removedContingent = fromHandles.filter(
      (h) => h.kind === "contingent" && !toHandleIds.has(h.id),
    );
    if (removedContingent.length > 0) {
      if (toHandleIds.size === 0) {
        return {
          ok: false,
          violation: "M1-unwitnessed-proxy",
          reason: `M1(iii) violation: target boundary "${req.toBoundary}" has no surviving handles (vacuous excision).`,
        };
      }
      const critVar =
        req.criterionVariable ??
        (req.originalUniversal.kind === "forall" ? req.originalUniversal.variable : "x");
      const survivingHandles = fromHandles.filter((h) => toHandleIds.has(h.id));
      const probeItems: Item[] = [];
      for (const h of survivingHandles) {
        probeItems.push(substituteHandle(req.criterionItem, critVar, h.id));
        if (req.originalUniversal.kind === "forall") {
          probeItems.push(
            substituteHandle(req.originalUniversal.body, req.originalUniversal.variable, h.id),
          );
        }
      }
      const critSnap = this.evaluate([req.originalUniversal, ...probeItems]);
      const hasInconsistentSurvivor = survivingHandles.some((h) => {
        const critInstance = substituteHandle(req.criterionItem, critVar, h.id);
        return critSnap.isLive(req.fromBoundary, "-", critInstance);
      });
      if (hasInconsistentSurvivor) {
        return {
          ok: false,
          violation: "M1-unwitnessed-proxy",
          reason: `M1(iii) violation: surviving handle in "${req.toBoundary}" witnesses negation of splitting criterion δ.`,
        };
      }
      const hasIndependentLiveWitness = survivingHandles.some((h) => {
        if (req.originalUniversal.kind === "forall") {
          const targetInstance = substituteHandle(
            req.originalUniversal.body,
            req.originalUniversal.variable,
            h.id,
          );
          const targetStatus = critSnap.localStatus(req.fromBoundary, targetInstance);
          if (targetStatus === "Excluded" || targetStatus === "Collision") {
            return false;
          }
        }
        const critInstance = substituteHandle(req.criterionItem, critVar, h.id);
        return critSnap.isLive(req.fromBoundary, "+", critInstance);
      });
      if (!hasIndependentLiveWitness) {
        return {
          ok: false,
          violation: "M1-unwitnessed-proxy",
          reason: `M1(iii) violation: splitting criterion lacks an independent Live positive witness (+δ) on a non-refuted surviving handle of "${req.toBoundary}".`,
        };
      }
    }

    // M1, domain binding: Dom(B') = {h ∈ Dom(B) : ¬Live -δ(h)}, and every excised handle carries
    // Live -δ(h) on B. A handle whose δ is Open stays in B'.
    const bindVar =
      req.criterionVariable ??
      (req.originalUniversal.kind === "forall" ? req.originalUniversal.variable : "x");
    const instanceOf = (h: string): Item => substituteHandle(req.criterionItem, bindVar, h);
    const bindSnap = this.evaluate([
      req.originalUniversal,
      ...fromHandles.map((h) => instanceOf(h.id)),
    ]);
    for (const h of fromHandles) {
      const excludedByCriterion = bindSnap.isLive(req.fromBoundary, "-", instanceOf(h.id));
      if (!toHandleIds.has(h.id) && !excludedByCriterion) {
        return {
          ok: false,
          violation: "M1-unbound-criterion",
          reason: `M1 domain binding violation: handle "${h.id}" is excised from "${req.fromBoundary}" without a Live exclusion of the splitting criterion δ(${h.id}).`,
        };
      }
      if (toHandleIds.has(h.id) && excludedByCriterion) {
        return {
          ok: false,
          violation: "M1-unbound-criterion",
          reason: `M1 domain binding violation: handle "${h.id}" is kept in "${req.toBoundary}" although δ(${h.id}) is Live excluded on "${req.fromBoundary}".`,
        };
      }
    }

    this.#track(req.originalUniversal);
    for (const h of fromHandles) {
      this.#track(instanceOf(h.id));
    }
    this.#refinements.push({
      fromBoundary: req.fromBoundary,
      toBoundary: req.toBoundary,
      criterionItem: req.criterionItem,
      criterionVariable: bindVar,
    });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:RefineBoundary(${req.fromBoundary} → ${req.toBoundary})`);
    this.#captureStage();
    return {
      ok: true,
      fromBoundary: req.fromBoundary,
      toBoundary: req.toBoundary,
      originalStatusBefore: statusBefore,
      originalExcludedPreserved: true,
    };
  }

  /** Evaluate Π(Σ) for the current Σ with the query set Q = extraItems. */
  evaluate(extraItems: readonly Item[] = []): EvaluationSnapshot {
    this.#syncBoundaries();
    const currentRecord = this.#stageArchive.get(this.#stage);
    if (currentRecord === undefined) {
      throw new Error(`Missing archived inquiry stage ${this.#stage}.`);
    }
    return this.#evaluateRecord({ ...currentRecord, boundarySnapshot: this.boundaries }, extraItems);
  }

  /** Evaluate the frozen historical inquiry state at `stage` (0 <= stage <= current stage). */
  evaluateAtStage(stage: number, extraItems: readonly Item[] = []): EvaluationSnapshot {
    this.#syncBoundaries();
    if (!Number.isInteger(stage) || stage < 0 || stage > this.#stage) {
      throw new Error(`Invalid stage ${stage}; expected integer in [0, ${this.#stage}].`);
    }
    const record = this.#stageArchive.get(stage);
    if (record === undefined) {
      throw new Error(`Missing archived inquiry stage ${stage}.`);
    }
    return this.#evaluateRecord(record, extraItems);
  }

  #evaluateRecord(record: StageRecord, extraItems: readonly Item[] = []): EvaluationSnapshot {
    const bounds = record.boundarySnapshot;
    const boundaries = bounds.nonEmptyBoundaries();
    const universe = buildUniverse(bounds, boundaries, [
      ...trackedItemsOf(record),
      ...extraItems,
    ]);

    // Structural reflection values (item 3): a stage-indexed reflection on a frozen earlier
    // stage receives the value its target judgment has there; other reflections receive none.
    const reflectionValues: { readonly item: Item; readonly polarity: Polarity }[] = [];
    for (const it of universe) {
      if (it.kind !== "refl" || it.targetStage === undefined) {
        continue;
      }
      if (!Number.isInteger(it.targetStage) || it.targetStage < 0 || it.targetStage >= record.stage) {
        continue;
      }
      if (!Number.isInteger(it.reflectedLevel) || it.reflectedLevel < computeItemLevel(it.targetItem)) {
        continue;
      }
      if (!this.isReflectionWellScopedAtStage(it.targetStage, it.targetBoundary, it.targetItem)) {
        continue;
      }
      const priorRecord = this.#stageArchive.get(it.targetStage);
      if (priorRecord === undefined) {
        continue;
      }
      const priorSnap = this.#evaluateRecord(priorRecord, [it.targetItem]);
      // A record whose authority is Undetermined at its stage gives the reflection no value, so the
      // reflection stays Open (core.md §1 item 3; audit-reflection-authority-flattening).
      if (
        it.targetStatus === undefined &&
        priorSnap.authorityOf(it.targetBoundary, it.targetPolarity, it.targetItem) === "Undetermined"
      ) {
        continue;
      }
      const holds =
        it.targetStatus !== undefined
          ? priorSnap.localStatus(it.targetBoundary, it.targetItem) === it.targetStatus
          : priorSnap.isLive(it.targetBoundary, it.targetPolarity, it.targetItem);
      reflectionValues.push({ item: it, polarity: holds ? "+" : "-" });
    }

    const report = evaluatePi({
      bounds,
      boundaries,
      universe,
      observations: [...record.baseObservations.values()],
      baseObservations: record.baseObservations,
      theorems: [...record.theorems.values()],
      incompatibilities: record.incompatibilities,
      collapses: record.structuralCollapses,
      closedDomains: record.closedDomains,
      reflectionValues,
    });
    const probe = new EvaluationSnapshot(report);
    const refinementObligations: RefinementObligation[] = [];
    for (const r of record.refinements) {
      for (const h of bounds.handlesOf(r.toBoundary)) {
        const instance = substituteHandle(r.criterionItem, r.criterionVariable, h.id);
        if (probe.isLive(r.fromBoundary, "-", instance)) {
          refinementObligations.push({
            fromBoundary: r.fromBoundary,
            toBoundary: r.toBoundary,
            handle: h.id,
            criterionKey: itemKey(instance),
          });
        }
      }
    }
    const overlapObligations: OverlapObligation[] = [];
    for (let i = 0; i < boundaries.length; i++) {
      for (let j = i + 1; j < boundaries.length; j++) {
        const left = boundaries[i] as string;
        const right = boundaries[j] as string;
        // The overlap of a pair is needed only when the pair holds opposite present records (item 14).
        const crossed = universe.filter(
          (item) =>
            (probe.hasRecord(left, "+", item) && probe.hasRecord(right, "-", item)) ||
            (probe.hasRecord(left, "-", item) && probe.hasRecord(right, "+", item)),
        );
        if (crossed.length === 0 || bounds.meetStatus(left, right).kind !== "unknown") {
          continue;
        }
        for (const item of crossed) {
          overlapObligations.push({ left, right, itemKey: itemKey(item) });
        }
      }
    }
    const coverObligations: CoverObligation[] = [];
    for (const c of bounds.registeredCovers()) {
      const validity = bounds.coverValidity(c.id);
      if (validity.kind !== "valid") {
        coverObligations.push({
          coverId: c.id,
          target: c.target,
          cells: c.cells,
          validity: validity.kind,
          witnesses: validity.witnesses,
        });
      }
    }
    return new EvaluationSnapshot(report, {
      refinement: refinementObligations,
      overlap: overlapObligations,
      cover: coverObligations,
    });
  }

  /**
   * M1(i), indirect reference (core.md §2 item 7): the relation of `criterion` from which
   * `+targetRelation` is reachable along the inferences item 14 fires, over literals (a relation
   * with a polarity): from the antecedent to the consequent of a conditional Live on `boundary` or
   * a boundary above it, and from one side of an incompatibility registered there to the exclusion
   * of the other. Shared consequences and shared exclusions do not link relations. Undefined when
   * no relation of the criterion reaches it.
   */
  #indirectLink(
    criterion: Item,
    targetRelation: string,
    boundary: string,
    snap: EvaluationSnapshot,
  ): string | undefined {
    const literals = (item: Item, positive: boolean, out: Set<string>): Set<string> => {
      switch (item.kind) {
        case "atom":
          out.add(`${positive ? "+" : "-"}${item.relation}`);
          break;
        case "flip":
          literals(item.inner, !positive, out);
          break;
        case "and":
        case "or":
          literals(item.left, positive, out);
          literals(item.right, positive, out);
          break;
        case "implies":
          literals(item.antecedent, !positive, out);
          literals(item.consequent, positive, out);
          break;
        case "forall":
        case "exists":
          literals(item.body, positive, out);
          break;
        default:
          break;
      }
      return out;
    };
    const lits = (item: Item): Set<string> => literals(item, true, new Set());
    const negated = (set: ReadonlySet<string>): Set<string> =>
      new Set([...set].map((l) => (l.startsWith("+") ? `-${l.slice(1)}` : `+${l.slice(1)}`)));
    const graph = new Map<string, Set<string>>();
    const connect = (from: ReadonlySet<string>, to: ReadonlySet<string>): void => {
      for (const a of from) {
        const set = graph.get(a) ?? new Set<string>();
        for (const b of to) {
          set.add(b);
        }
        graph.set(a, set);
      }
    };
    const inScope = (b: string): boolean => this.boundaries.refines(boundary, b);
    for (const inc of this.#incompatibilities) {
      if (inScope(inc.boundary)) {
        connect(lits(inc.left), negated(lits(inc.right)));
        connect(lits(inc.right), negated(lits(inc.left)));
      }
    }
    const bounds = this.boundaries.nonEmptyBoundaries().filter(inScope);
    const conditionals = buildUniverse(this.boundaries, this.boundaries.nonEmptyBoundaries(), [
      ...this.#trackedItems.values(),
    ]).filter((it) => it.kind === "implies");
    for (const imp of conditionals) {
      if (imp.kind === "implies" && bounds.some((b) => snap.isLive(b, "+", imp))) {
        connect(lits(imp.antecedent), lits(imp.consequent));
      }
    }
    const goal = `+${targetRelation}`;
    for (const startLit of lits(criterion)) {
      const seen = new Set<string>([startLit]);
      const queue = [startLit];
      while (queue.length > 0) {
        const cur = queue.shift() as string;
        if (cur === goal) {
          return startLit.slice(1);
        }
        for (const next of graph.get(cur) ?? []) {
          if (!seen.has(next)) {
            seen.add(next);
            queue.push(next);
          }
        }
      }
    }
    return undefined;
  }

  #addBaseObservation(
    boundary: string,
    polarity: Polarity,
    item: Item,
    baseId: string,
    handleAuth?: HandleAuth,
  ): void {
    this.#syncBoundaries();
    this.boundaries.nonEmptySubBoundaries(boundary);
    if (this.#usedBaseIds.has(baseId)) {
      throw new Error(
        `Base identifier "${baseId}" is already used in this inquiry; identifiers name one observation for the life of the inquiry, also after Retract.`,
      );
    }
    if (handleAuth !== undefined) {
      if (!this.boundaries.isAdmissibleHandle(boundary, handleAuth.handle, handleAuth.criterion)) {
        throw new Error(
          `Anti-Equivocation violation: handle "${handleAuth.handle}" with criterion "${handleAuth.criterion}" is not admissible in "${boundary}".`,
        );
      }
    }
    // Observe± is many-sorted (core.md §2 item 6): every handle the item names belongs to Dom(B),
    // where Dom(⊤_B) is the union of the domains of the declared boundaries.
    const domain = new Set(this.boundaries.handlesOf(boundary).map((h) => h.id));
    const foreign = [...collectHandles(item)].find((h) => !domain.has(h));
    if (foreign !== undefined) {
      throw new Error(
        `Many-sorted observation: handle "${foreign}" of ${itemKey(item)} is not in Dom("${boundary}") (core.md §2 item 6).`,
      );
    }
    this.#track(item);
    const key = itemKey(item);
    this.#usedBaseIds.add(baseId);
    this.#baseObservations.set(baseId, { baseId, boundary, polarity, item, key });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Observe${polarity}(${boundary}, ${key}, ${baseId})`);
    this.#captureStage();
  }

  #isDefinedNonEmptyBoundary(bounds: BoundarySystem, boundary: string): boolean {
    if (boundary === BOT_BOUNDARY) {
      return false;
    }
    try {
      return bounds.refines(boundary, boundary);
    } catch {
      return false;
    }
  }

  #captureStage(): void {
    this.#stageArchive.set(this.#stage, {
      stage: this.#stage,
      baseObservations: new Map(this.#baseObservations),
      theorems: new Map(this.#theorems),
      incompatibilities: [...this.#incompatibilities],
      structuralCollapses: [...this.#structuralCollapses],
      closedDomains: this.#closedDomains(this.boundaries),
      refinements: [...this.#refinements],
      trackedItems: new Map(this.#trackedItems),
      boundarySnapshot: this.boundaries.clone(),
    });
    this.#boundaryVersion = this.boundaries.version;
  }

  /** Track an item named by a transition; it stays tracked after a Retract (item 14). */
  #track(item: Item): void {
    const key = itemKey(item);
    if (!this.#trackedItems.has(key)) {
      this.#trackedItems.set(key, item);
    }
  }
}

/** The handle set of Dom(domain) in `bounds`, as a signature a closure anchors. */
function handleSignature(bounds: BoundarySystem, domain: string): string {
  return bounds
    .handlesOf(domain)
    .map((h) => h.id)
    .sort()
    .join("\0");
}

/**
 * The items tracked by Σ (item 14): ⊥ and every item named by a transition in the history of
 * Σ, retracted ones included: the items of base observations and recorded theorems (the
 * conclusion and the grounds it cites), both sides of each incompatibility, and both A and
 * A → ⊥ for each structural collapse B ⊓ [A] = ⊥_B.
 */
function trackedItemsOf(record: StageRecord): Item[] {
  return [...record.trackedItems.values()];
}

/**
 * U(Σ, Q) (item 14): the tracked and queried items, closed under direct sub-items, under
 * quantifier instances A(w) and δ(w) for w ∈ Dom(D) (a quantifier contributes its instances,
 * not its open body), and under congruence rewrites that replace the handle at one position
 * of a relational atom or of an `≈` item by a handle of a boundary in 𝔅(Σ). A polarity flip
 * belongs to U(Σ, Q) exactly when it arises in this way; no member is ever prefixed with `~`.
 * Reflections and named references have no direct sub-items.
 */
function buildUniverse(
  bounds: BoundarySystem,
  boundaries: readonly string[],
  roots: readonly Item[],
): Item[] {
  const handleSet = new Set<string>();
  for (const b of boundaries) {
    for (const h of bounds.handlesOf(b)) {
      handleSet.add(h.id);
    }
  }
  const handles = [...handleSet].sort();

  const items: Item[] = [];
  const seen = new Set<string>();
  const work: Item[] = [];
  const add = (item: Item): void => {
    const key = itemKey(item);
    if (!seen.has(key)) {
      seen.add(key);
      items.push(item);
      work.push(item);
    }
  };
  for (const root of roots) {
    add(root);
  }
  for (let item = work.pop(); item !== undefined; item = work.pop()) {
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
      case "exists":
        for (const h of bounds.handlesOf(item.domain)) {
          add(substituteHandle(item.body, item.variable, h.id));
          if (item.domainConstraint !== undefined) {
            add(substituteHandle(item.domainConstraint, item.variable, h.id));
          }
        }
        break;
      case "atom": {
        const { relation, roles } = item;
        for (let position = 0; position < roles.length; position++) {
          for (const u of handles) {
            add(
              atom(
                relation,
                roles.map((r, j) => (j === position ? { role: r.role, handle: u } : r)),
              ),
            );
          }
        }
        break;
      }
      case "equiv":
        for (const u of handles) {
          add(equiv(item.boundary, u, item.right));
          add(equiv(item.boundary, item.left, u));
        }
        break;
      case "bottom":
      case "refl":
      case "ref":
        break;
    }
  }
  return items;
}

/** Inputs of Π(Σ) for one inquiry state and query set. */
type PiInput = {
  readonly bounds: BoundarySystem;
  /** 𝔅(Σ): the non-empty boundaries declared in Σ, ⊤_B included. */
  readonly boundaries: readonly string[];
  /** U(Σ, Q). */
  readonly universe: readonly Item[];
  readonly observations: readonly BaseObservation[];
  readonly baseObservations: ReadonlyMap<string, BaseObservation>;
  readonly theorems: readonly RecordedTheorem[];
  readonly incompatibilities: readonly IncompatibilityConstraint[];
  readonly collapses: readonly StructuralCollapse[];
  readonly closedDomains: ReadonlySet<string>;
  readonly reflectionValues: readonly { readonly item: Item; readonly polarity: Polarity }[];
};

/**
 * A premise of a rule instance. `live` marks a `Live` premise (live atom); otherwise it is a
 * record premise (rec atom). `baseId` pins the witnessing entry of a Theorem's base premise.
 */
type Prem = {
  readonly slot: number;
  readonly p: Polarity;
  readonly live: boolean;
  readonly baseId: string | null;
};

/** A ground rule instance of Π(Σ) with conclusion (slot, p). */
type Instance = {
  readonly slot: number;
  readonly p: Polarity;
  /** Premises that must all hold. */
  readonly prems: readonly Prem[];
  /** Requirements met by any one of their alternatives, each a conjunction of premises. */
  readonly choices: readonly (readonly (readonly Prem[])[])[];
  readonly rule: string;
  readonly origin: "base" | "structural" | "derived";
  readonly baseId: string | null;
  readonly structural: StructuralRule | null;
  /** Extra provenance leaf (incompatibility, theorem or domain closure). */
  readonly tag: string | null;
  readonly coverCells: readonly string[] | null;
  /** Witness enumeration takes one derivation per instance instead of every combination. */
  readonly firstOnly: boolean;
};

/** Hard bound on witnessing entries; exceeding it is reported, never truncated (G6). */
const MAX_PROVENANCE_ENTRIES = 250_000;

/**
 * Ground Π(Σ) over 𝔅(Σ) × U(Σ, Q), compute its well-founded model, and build the entries
 * that witness its true atoms (spec/core.md §5 item 14).
 */
function evaluatePi(input: PiInput): PiReport {
  const { bounds, boundaries, universe } = input;
  const nb = boundaries.length;
  const nu = universe.length;
  const nS = nb * nu;
  const bIndex = new Map(boundaries.map((b, i) => [b, i] as const));
  const uIndex = new Map(universe.map((it, i) => [itemKey(it), i] as const));
  const idx = (item: Item): number | undefined => uIndex.get(itemKey(item));
  const slotOf = (b: number, a: number): number => b * nu + a;
  const boundaryOf = (s: number): string => boundaries[Math.floor(s / nu)] ?? BOT_BOUNDARY;
  const itemOf = (s: number): Item => {
    const it = universe[s % nu];
    if (it === undefined) {
      throw new Error(`Π(Σ): internal error, slot ${s} out of range.`);
    }
    return it;
  };

  // ------------------------------------------------------------ boundary algebra over 𝔅(Σ)
  const subsOf: number[][] = boundaries.map((sup) => {
    const subs: number[] = [];
    boundaries.forEach((sub, j) => {
      if (bounds.refines(sub, sup)) {
        subs.push(j);
      }
    });
    return subs;
  });
  const subsOfName = (name: string): readonly number[] => {
    const i = bIndex.get(name);
    if (i !== undefined) {
      return subsOf[i] ?? [];
    }
    return [];
  };

  const MEET_BOTTOM = -1;
  const MEET_AMBIGUOUS = -2;
  // An unknown overlap (core.md §2 item 4) licenses no Scoped Cut.
  const MEET_UNKNOWN = -3;
  const meetTable = new Int32Array(nb * nb);
  const meetErrors = new Map<number, string>();
  // Scoped Cut instances over an ambiguous pair, left out of the program until shown needed.
  const ambiguousCuts: { readonly key: number; readonly antecedent: number; readonly conditional: number }[] = [];
  for (let b1 = 0; b1 < nb; b1++) {
    for (let b2 = 0; b2 < nb; b2++) {
      const n1 = boundaries[b1] ?? BOT_BOUNDARY;
      const n2 = boundaries[b2] ?? BOT_BOUNDARY;
      let status: MeetStatus;
      try {
        status = bounds.meetStatus(n1, n2);
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        if (!message.startsWith("Ambiguous meet")) {
          throw error;
        }
        meetTable[b1 * nb + b2] = MEET_AMBIGUOUS;
        meetErrors.set(b1 * nb + b2, message);
        continue;
      }
      meetTable[b1 * nb + b2] =
        status.kind === "overlap"
          ? (bIndex.get(status.meet) ?? MEET_BOTTOM)
          : status.kind === "unknown"
            ? MEET_UNKNOWN
            : MEET_BOTTOM;
    }
  }

  // The witnessed covers of item 5.
  const coversOf: { readonly names: readonly string[]; readonly cells: readonly number[] }[][] =
    boundaries.map((b) =>
      bounds.witnessedCoversOf(b).map((names) => ({
        names,
        cells: names.map((c) => {
          const i = bIndex.get(c);
          if (i === undefined) {
            throw new Error(`Π(Σ): cover cell "${c}" of "${b}" is not a non-empty boundary.`);
          }
          return i;
        }),
      })),
    );

  // ------------------------------------------------------------ ground rule instances
  const instances: Instance[] = [];
  const rec = (b: number, p: Polarity, a: number | undefined): Prem | undefined =>
    a === undefined ? undefined : { slot: slotOf(b, a), p, live: false, baseId: null };
  const lv = (b: number, p: Polarity, a: number | undefined): Prem | undefined =>
    a === undefined ? undefined : { slot: slotOf(b, a), p, live: true, baseId: null };

  type InstanceSpec = {
    readonly rule: string;
    readonly origin?: "base" | "structural";
    readonly baseId?: string;
    readonly structural?: StructuralRule;
    readonly tag?: string;
    readonly coverCells?: readonly string[];
    readonly firstOnly?: boolean;
    readonly choices?: readonly (readonly (readonly (Prem | undefined)[])[])[];
  };

  /**
   * Add one instance with conclusion (b, p, a). A conclusion or a premise outside U(Σ, Q) has
   * no atom: the instance does not exist, and an alternative naming such a premise is dropped.
   */
  const emit = (
    b: number | undefined,
    p: Polarity,
    a: number | undefined,
    prems: readonly (Prem | undefined)[],
    spec: InstanceSpec,
  ): void => {
    if (b === undefined || a === undefined) {
      return;
    }
    const concrete: Prem[] = [];
    for (const pr of prems) {
      if (pr === undefined) {
        return;
      }
      concrete.push(pr);
    }
    const choices: (readonly Prem[])[][] = [];
    for (const req of spec.choices ?? []) {
      const alternatives: (readonly Prem[])[] = [];
      for (const alt of req) {
        if (alt.every((pr) => pr !== undefined)) {
          alternatives.push(alt as readonly Prem[]);
        }
      }
      if (alternatives.length === 0) {
        return;
      }
      if (alternatives.length === 1) {
        concrete.push(...(alternatives[0] ?? []));
      } else {
        choices.push(alternatives);
      }
    }
    instances.push({
      slot: slotOf(b, a),
      p,
      prems: concrete,
      choices,
      rule: spec.rule,
      origin: spec.origin ?? "derived",
      baseId: spec.baseId ?? null,
      structural: spec.structural ?? null,
      tag: spec.tag ?? null,
      coverCells: spec.coverCells ?? null,
      firstOnly: spec.firstOnly ?? false,
    });
  };
  const allB = boundaries.map((_, i) => i);
  const POLARITIES: readonly Polarity[] = ["+", "-"];
  const opposite = (p: Polarity): Polarity => (p === "+" ? "-" : "+");

  // Base: Observe±(B, A, w) in G±.
  for (const o of input.observations) {
    emit(bIndex.get(o.boundary), o.polarity, idx(o.item), [], {
      rule: "base",
      origin: "base",
      baseId: o.baseId,
    });
  }

  // Theorem: record premises are the base records it requires, Live premises the grounds; it fires
  // only while every cover its derivation used is witnessed (core.md §5 item 14).
  for (const thm of input.theorems) {
    if (!thm.requiredCovers.every((c) => input.bounds.isWitnessedCover(c.boundary, c.cells))) {
      continue;
    }
    const prems: (Prem | undefined)[] = [];
    let complete = true;
    for (const baseId of thm.requiredBaseIds) {
      const base = input.baseObservations.get(baseId);
      const bb = base !== undefined ? bIndex.get(base.boundary) : undefined;
      const ba = base !== undefined ? idx(base.item) : undefined;
      if (base === undefined || bb === undefined || ba === undefined) {
        complete = false;
        break;
      }
      prems.push({ slot: slotOf(bb, ba), p: base.polarity, live: false, baseId });
    }
    if (!complete) {
      continue;
    }
    for (const dep of thm.requiredGrounds) {
      const db = bIndex.get(dep.boundary);
      prems.push(db === undefined ? undefined : lv(db, dep.polarity, idx(dep.item)));
    }
    emit(bIndex.get(thm.boundary), thm.polarity, idx(thm.item), prems, {
      rule: "theorem",
      tag: `@thm:${thm.theoremId}`,
    });
  }

  // Structural: (B, -, ⊥) on every B; a collapse on its own B; t ≈_B t; reflection values.
  const bottomIdx = idx(bottom());
  for (const b of allB) {
    emit(b, "-", bottomIdx, [], { rule: "bottom-excl", origin: "structural", structural: "bottom-excl" });
  }
  for (const c of input.collapses) {
    const b = bIndex.get(c.boundary);
    const spec: InstanceSpec = { rule: "struct-imposs", origin: "structural", structural: "struct-imposs" };
    emit(b, "+", idx(implies(c.item, bottom())), [], spec);
    emit(b, "-", idx(c.item), [], spec);
  }
  for (const rv of input.reflectionValues) {
    for (const b of allB) {
      emit(b, rv.polarity, idx(rv.item), [], { rule: "refl-eval", origin: "structural", structural: "refl-eval" });
    }
  }

  // Downward heredity: (B', p, A) from the record (B, p, A), B' ⊑ B.
  for (const b of allB) {
    for (const sub of subsOf[b] ?? []) {
      if (sub === b) {
        continue;
      }
      for (let a = 0; a < nu; a++) {
        for (const p of POLARITIES) {
          emit(sub, p, a, [rec(b, p, a)], { rule: "down" });
        }
      }
    }
  }

  // Indexes for the item-shape rules.
  type EquivItem = Extract<Item, { kind: "equiv" }>;
  type AtomItem = Extract<Item, { kind: "atom" }>;
  const equivs: { readonly item: EquivItem; readonly a: number }[] = [];
  const atomsByHandle = new Map<string, { readonly item: AtomItem; readonly a: number }[]>();
  const implicationsByAntecedent = new Map<string, Map<string, number>>();
  universe.forEach((item, a) => {
    if (item.kind === "equiv") {
      equivs.push({ item, a });
    } else if (item.kind === "atom") {
      for (const h of new Set(item.roles.map((r) => r.handle))) {
        const list = atomsByHandle.get(h) ?? [];
        list.push({ item, a });
        atomsByHandle.set(h, list);
      }
    } else if (item.kind === "implies") {
      const key = itemKey(item.antecedent);
      const byConsequent = implicationsByAntecedent.get(key) ?? new Map<string, number>();
      byConsequent.set(itemKey(item.consequent), a);
      implicationsByAntecedent.set(key, byConsequent);
    }
  });

  /** Scoped Cut instances that need an ambiguous meet, checked against the program's reach. */

  universe.forEach((item, a) => {
    switch (item.kind) {
      case "flip": {
        const inner = idx(item.inner);
        for (const b of allB) {
          for (const p of POLARITIES) {
            emit(b, opposite(p), a, [rec(b, p, inner)], { rule: "flip" });
            emit(b, opposite(p), inner, [rec(b, p, a)], { rule: "flip-elim" });
          }
        }
        break;
      }
      case "and": {
        const left = idx(item.left);
        const right = idx(item.right);
        for (const b of allB) {
          emit(b, "+", a, [lv(b, "+", left), lv(b, "+", right)], { rule: "and-intro" });
          emit(b, "+", left, [lv(b, "+", a)], { rule: "and-elim-l" });
          emit(b, "+", right, [lv(b, "+", a)], { rule: "and-elim-r" });
          emit(b, "-", a, [rec(b, "-", left)], { rule: "and-excl-l" });
          emit(b, "-", a, [rec(b, "-", right)], { rule: "and-excl-r" });
        }
        break;
      }
      case "or": {
        const left = idx(item.left);
        const right = idx(item.right);
        for (const b of allB) {
          // ∨ by cover, the identity cover {B} included.
          for (const cover of coversOf[b] ?? []) {
            emit(b, "+", a, [], {
              rule: "or-cover",
              coverCells: cover.names,
              firstOnly: true,
              choices: cover.cells.map((c) =>
                left === right ? [[lv(c, "+", left)]] : [[lv(c, "+", left)], [lv(c, "+", right)]],
              ),
            });
          }
          emit(b, "-", a, [rec(b, "-", left), rec(b, "-", right)], { rule: "or-excl" });
        }
        // ∨E for every E with A → E and C → E in U(Σ, Q).
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
              emit(b, "+", e, [lv(b, "+", a), lv(b, "+", leftImpl), lv(b, "+", rightImpl)], {
                rule: "or-elim",
              });
            }
          }
        }
        break;
      }
      case "implies": {
        const antecedent = idx(item.antecedent);
        const consequent = idx(item.consequent);
        // Scoped Cut: (B₁ ⊓ B₂, +, C) from Live (B₁, +, A) and Live (B₂, +, A → C).
        for (const b1 of allB) {
          for (const b2 of allB) {
            const m = meetTable[b1 * nb + b2] ?? MEET_BOTTOM;
            if (m === MEET_BOTTOM || m === MEET_UNKNOWN) {
              continue;
            }
            if (m === MEET_AMBIGUOUS) {
              if (antecedent !== undefined) {
                ambiguousCuts.push({
                  key: b1 * nb + b2,
                  antecedent: slotOf(b1, antecedent),
                  conditional: slotOf(b2, a),
                });
              }
              continue;
            }
            emit(m, "+", consequent, [lv(b1, "+", antecedent), lv(b2, "+", a)], { rule: "mp" });
          }
        }
        for (const b of allB) {
          // Counterexample: record (B, -, C) with Live (B, +, A).
          emit(b, "-", a, [rec(b, "-", consequent), lv(b, "+", antecedent)], {
            rule: "counter-implies",
          });
          // imposs-excl: Live (B, +, A → ⊥) gives (B, -, A).
          if (item.consequent.kind === "bottom") {
            emit(b, "-", antecedent, [lv(b, "+", a)], { rule: "imposs-excl" });
          }
        }
        break;
      }
      case "forall":
      case "exists": {
        const constraint = item.domainConstraint;
        const instancesOf = bounds.handlesOf(item.domain).map((h) => ({
          body: idx(substituteHandle(item.body, item.variable, h.id)),
          delta:
            constraint !== undefined
              ? idx(substituteHandle(constraint, item.variable, h.id))
              : undefined,
        }));
        // Enumeration needs CloseDomain(D) in C_B and D ≠ ⊥_B; an empty closed Dom(D) is vacuous.
        const closed = item.domain !== BOT_BOUNDARY && input.closedDomains.has(item.domain);
        const closureTag = `@closure:${item.domain}`;
        for (const b of allB) {
          const plusDelta = (delta: number | undefined): (Prem | undefined)[] =>
            constraint !== undefined ? [lv(b, "+", delta)] : [];
          if (item.kind === "forall") {
            for (const { body, delta } of instancesOf) {
              emit(b, "+", body, [lv(b, "+", a), ...plusDelta(delta)], { rule: "forall-elim" });
              emit(b, "-", a, [rec(b, "-", body), ...plusDelta(delta)], { rule: "forall-counter" });
            }
            if (closed) {
              emit(b, "+", a, [], {
                rule: "forall-generic",
                tag: closureTag,
                firstOnly: true,
                choices: instancesOf.map(({ body, delta }) =>
                  constraint !== undefined
                    ? [[lv(b, "-", delta)], [lv(b, "+", body), lv(b, "+", delta)]]
                    : [[lv(b, "+", body)]],
                ),
              });
            }
          } else {
            for (const { body, delta } of instancesOf) {
              emit(b, "+", a, [lv(b, "+", body), ...plusDelta(delta)], { rule: "exists-intro" });
            }
            if (closed) {
              emit(b, "-", a, [], {
                rule: "exists-excl",
                tag: closureTag,
                firstOnly: true,
                choices: instancesOf.map(({ body, delta }) =>
                  constraint !== undefined
                    ? [[rec(b, "-", body)], [lv(b, "-", delta)]]
                    : [[rec(b, "-", body)]],
                ),
              });
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

  // Incompatibility A ⊥_B C on every B' ⊑ B, in both directions.
  for (const c of input.incompatibilities) {
    const left = idx(c.left);
    const right = idx(c.right);
    const tag = `@incompat:${itemKey(c.left)}⊥${itemKey(c.right)}`;
    for (const sub of subsOfName(c.boundary)) {
      emit(sub, "-", right, [lv(sub, "+", left)], { rule: "incompat", tag });
      emit(sub, "-", left, [lv(sub, "+", right)], { rule: "incompat", tag });
    }
  }

  // Congruence items: reflexivity, ≈ symmetry and transitivity, Congruence.
  const equivsByLeft = new Map<string, { readonly item: EquivItem; readonly a: number }[]>();
  for (const e of equivs) {
    const key = `${e.item.boundary}\u0000${e.item.left}`;
    const list = equivsByLeft.get(key) ?? [];
    list.push(e);
    equivsByLeft.set(key, list);
  }
  for (const { item, a } of equivs) {
    const d = item.boundary;
    const dIndex = bIndex.get(d);
    // Structural: (B, +, t ≈_B t) for t ∈ Dom(B), on its own boundary.
    if (item.left === item.right && dIndex !== undefined && bounds.isAdmissibleHandle(d, item.left)) {
      emit(dIndex, "+", a, [], { rule: "equiv-refl", origin: "structural", structural: "equiv-refl" });
    }
    if (item.left !== item.right) {
      const swapped = idx(equiv(d, item.right, item.left));
      for (const b of allB) {
        emit(b, "+", swapped, [lv(b, "+", a)], { rule: "equiv-sym" });
      }
    }
    for (const next of equivsByLeft.get(`${d}\u0000${item.right}`) ?? []) {
      const target = idx(equiv(d, item.left, next.item.right));
      if (target === a || target === next.a) {
        continue; // the conclusion is one of its own premises
      }
      for (const b of allB) {
        emit(b, "+", target, [lv(b, "+", a), lv(b, "+", next.a)], { rule: "equiv-trans" });
      }
    }
    // Congruence: one occurrence of t in a relational atom native to D, on every B ⊑ D.
    if (item.left === item.right || dIndex === undefined) {
      continue;
    }
    const subs = subsOf[dIndex] ?? [];
    for (const r of atomsByHandle.get(item.left) ?? []) {
      if (!bounds.hasNativeRelation(d, r.item.relation)) {
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
            emit(b, p, target, [lv(b, "+", a), lv(b, p, r.a)], { rule: "congruence" });
          }
        }
      });
    }
  }

  // Cover-Gluing: (B, p, A) from Live (Bᵢ, p, A) on every cell of {Bᵢ} ▷ B other than {B}.
  for (const b of allB) {
    for (const cover of coversOf[b] ?? []) {
      if (cover.cells.length === 1 && cover.cells[0] === b) {
        continue;
      }
      for (let a = 0; a < nu; a++) {
        for (const p of POLARITIES) {
          emit(
            b,
            p,
            a,
            cover.cells.map((c) => lv(c, p, a)),
            { rule: "cover-glue", coverCells: cover.names, firstOnly: true },
          );
        }
      }
    }
  }

  // ------------------------------------------------------------ the ground program
  // Atoms: rec(+) [0, nS), rec(-) [nS, 2nS), live(+) [2nS, 3nS), live(-) [3nS, 4nS), then
  // auxiliary atoms for requirements with several alternatives (positive clauses only, which
  // leaves the well-founded model of the original atoms unchanged).
  const recAtom = (p: Polarity, s: number): number => (p === "+" ? 0 : nS) + s;
  const liveAtom = (p: Polarity, s: number): number => 2 * nS + (p === "+" ? 0 : nS) + s;
  const premRecAtom = (pr: Prem): number => (pr.live ? liveAtom(pr.p, pr.slot) : recAtom(pr.p, pr.slot));
  const premLiveAtom = (pr: Prem): number => liveAtom(pr.p, pr.slot);

  let atomCount = 4 * nS;
  const heads: number[] = [];
  const guards: number[] = [];
  const bodyStart: number[] = [0];
  const bodyAtoms: number[] = [];
  const addClause = (head: number, body: readonly number[], guard: number): void => {
    heads.push(head);
    guards.push(guard);
    for (const x of body) {
      bodyAtoms.push(x);
    }
    bodyStart.push(bodyAtoms.length);
  };
  for (const inst of instances) {
    const recBody = inst.prems.map(premRecAtom);
    const liveBody = inst.prems.map(premLiveAtom);
    for (const alternatives of inst.choices) {
      const auxRec = atomCount++;
      const auxLive = atomCount++;
      for (const alt of alternatives) {
        addClause(auxRec, alt.map(premRecAtom), -1);
        addClause(auxLive, alt.map(premLiveAtom), -1);
      }
      recBody.push(auxRec);
      liveBody.push(auxLive);
    }
    // rec(B, p, A) ← rec(P) for P ∈ R, live(P) for P ∈ L
    addClause(recAtom(inst.p, inst.slot), recBody, -1);
    // live(B, p, A) ← live(P) for P ∈ R ∪ L, not obs(B, A)
    addClause(liveAtom(inst.p, inst.slot), liveBody, inst.slot);
  }

  const nClauses = heads.length;
  const headArr = Int32Array.from(heads);
  const guardArr = Int32Array.from(guards);
  const startArr = Int32Array.from(bodyStart);
  const bodyArr = Int32Array.from(bodyAtoms);
  // Occurrence lists (compressed): the clauses in whose body each atom appears.
  const occStart = new Int32Array(atomCount + 1);
  for (const x of bodyArr) {
    occStart[x + 1] = (occStart[x + 1] ?? 0) + 1;
  }
  for (let x = 0; x < atomCount; x++) {
    occStart[x + 1] = (occStart[x + 1] ?? 0) + (occStart[x] ?? 0);
  }
  const occClauses = new Int32Array(bodyArr.length);
  const fill = occStart.slice(0, atomCount);
  for (let c = 0; c < nClauses; c++) {
    for (let k = startArr[c] ?? 0; k < (startArr[c + 1] ?? 0); k++) {
      const x = bodyArr[k] ?? 0;
      const pos = fill[x] ?? 0;
      occClauses[pos] = c;
      fill[x] = pos + 1;
    }
  }

  /** Least model of the program with each `not obs(s)` read as false where assumedObs[s] = 1. */
  const leastModel = (assumedObs: Uint8Array): Uint8Array => {
    const truth = new Uint8Array(atomCount);
    const remaining = new Int32Array(nClauses);
    const stack = new Int32Array(atomCount);
    let sp = 0;
    const fire = (x: number): void => {
      if (truth[x] !== 1) {
        truth[x] = 1;
        stack[sp++] = x;
      }
    };
    for (let c = 0; c < nClauses; c++) {
      const guard = guardArr[c] ?? -1;
      if (guard >= 0 && assumedObs[guard] === 1) {
        remaining[c] = -1;
        continue;
      }
      const length = (startArr[c + 1] ?? 0) - (startArr[c] ?? 0);
      remaining[c] = length;
      if (length === 0) {
        fire(headArr[c] ?? 0);
      }
    }
    while (sp > 0) {
      const x = stack[--sp] ?? 0;
      for (let k = occStart[x] ?? 0; k < (occStart[x + 1] ?? 0); k++) {
        const c = occClauses[k] ?? 0;
        const left = remaining[c] ?? 0;
        if (left > 0) {
          remaining[c] = left - 1;
          if (left === 1) {
            fire(headArr[c] ?? 0);
          }
        }
      }
    }
    return truth;
  };

  type Interpretation = {
    readonly truth: Uint8Array;
    readonly coll: Uint8Array;
    readonly obs: Uint8Array;
  };
  /** Γ(J): the least model under J's obs atoms, extended with its coll and obs atoms. */
  const gamma = (assumedObs: Uint8Array): Interpretation => {
    const truth = leastModel(assumedObs);
    const coll = new Uint8Array(nS);
    for (let s = 0; s < nS; s++) {
      coll[s] = truth[s] === 1 && truth[nS + s] === 1 ? 1 : 0;
    }
    // obs(B, A) ← coll(B', A) for every B' ∈ 𝔅(Σ) with B' ⊑ B (⊑ reflexive).
    const obs = new Uint8Array(nS);
    for (let b = 0; b < nb; b++) {
      for (const sub of subsOf[b] ?? []) {
        for (let a = 0; a < nu; a++) {
          if (coll[sub * nu + a] === 1) {
            obs[b * nu + a] = 1;
          }
        }
      }
    }
    return { truth, coll, obs };
  };

  // Alternating fixpoint: under rises from ∅ to the true atoms, over = Γ(under) falls to the
  // atoms that are true or undefined.
  let under: Interpretation = {
    truth: new Uint8Array(atomCount),
    coll: new Uint8Array(nS),
    obs: new Uint8Array(nS),
  };
  let over = gamma(under.obs);

  // A Scoped Cut instance over an ambiguous pair needs the meet when its Live premises are true in
  // the least model read with every obs atom false and without such instances (item 14, Role):
  // otherwise it can never fire, and its conclusion boundary decides nothing.
  for (const cut of ambiguousCuts) {
    if (
      over.truth[liveAtom("+", cut.antecedent)] === 1 &&
      over.truth[liveAtom("+", cut.conditional)] === 1
    ) {
      throw new Error(
        `Π(Σ): Scoped Cut needs the meet of "${boundaryOf(cut.antecedent)}" and "${boundaryOf(cut.conditional)}", which is ambiguous (${meetErrors.get(cut.key) ?? "ambiguous meet"}).`,
      );
    }
  }

  const sameTruth = (x: Uint8Array, y: Uint8Array): boolean => {
    for (let i = 0; i < x.length; i++) {
      if (x[i] !== y[i]) {
        return false;
      }
    }
    return true;
  };
  const maxRounds = 2 * atomCount + 4;
  for (let round = 0; ; round++) {
    if (round > maxRounds) {
      throw new Error(`Π(Σ): the alternating fixpoint did not converge within ${maxRounds} rounds.`);
    }
    const next = gamma(over.obs);
    if (sameTruth(next.truth, under.truth)) {
      break;
    }
    under = next;
    over = gamma(under.obs);
  }
  for (let x = 0; x < atomCount; x++) {
    if (under.truth[x] === 1 && over.truth[x] !== 1) {
      throw new Error("Π(Σ): internal error, a true atom is missing from Γ(true).");
    }
  }

  const code = (u: Uint8Array, o: Uint8Array, i: number): number =>
    u[i] === 1 ? TRUE : o[i] === 1 ? UNDEFINED : FALSE;
  const recCodes: [Uint8Array, Uint8Array] = [new Uint8Array(nS), new Uint8Array(nS)];
  const liveCodes: [Uint8Array, Uint8Array] = [new Uint8Array(nS), new Uint8Array(nS)];
  const collCodes = new Uint8Array(nS);
  const obsCodes = new Uint8Array(nS);
  for (let s = 0; s < nS; s++) {
    recCodes[0][s] = code(under.truth, over.truth, recAtom("+", s));
    recCodes[1][s] = code(under.truth, over.truth, recAtom("-", s));
    liveCodes[0][s] = code(under.truth, over.truth, liveAtom("+", s));
    liveCodes[1][s] = code(under.truth, over.truth, liveAtom("-", s));
    collCodes[s] = code(under.coll, over.coll, s);
    obsCodes[s] = code(under.obs, over.obs, s);
  }

  // ------------------------------------------------------------ witnessing entries
  const entries: GroundEntry[] = [];
  const entryLeaves: (readonly string[])[] = [];
  const entryLive: boolean[] = [];
  const allByKey: (number[] | undefined)[] = new Array<number[] | undefined>(2 * nS);
  const liveByKey: (number[] | undefined)[] = new Array<number[] | undefined>(2 * nS);
  const dedup = new Set<string>();
  const instancesByPrem: (number[] | undefined)[] = new Array<number[] | undefined>(2 * nS);
  const premKey = (pr: Prem): number => pr.slot * 2 + polIndex(pr.p);
  instances.forEach((inst, i) => {
    const keys = new Set<number>();
    for (const pr of inst.prems) {
      keys.add(premKey(pr));
    }
    for (const alternatives of inst.choices) {
      for (const alt of alternatives) {
        for (const pr of alt) {
          keys.add(premKey(pr));
        }
      }
    }
    for (const k of keys) {
      const list = instancesByPrem[k] ?? [];
      list.push(i);
      instancesByPrem[k] = list;
    }
  });

  const candidates = (pr: Prem, phase: 1 | 2): readonly number[] => {
    const k = premKey(pr);
    const list = (phase === 1 || pr.live ? liveByKey[k] : allByKey[k]) ?? [];
    if (pr.baseId === null) {
      return list;
    }
    return list.filter((e) => {
      const prov = entries[e]?.provenance;
      return prov?.kind === "base" && prov.baseId === pr.baseId;
    });
  };

  const fresh: number[] = [];
  const addEntry = (inst: Instance, deps: readonly number[], phase: 1 | 2): void => {
    const s = inst.slot;
    const pi = polIndex(inst.p);
    let leaves: readonly string[];
    if (inst.origin === "base") {
      leaves = [inst.baseId ?? ""];
    } else if (inst.origin === "structural") {
      leaves = [`@${inst.structural ?? inst.rule}`];
    } else {
      const set = new Set<string>();
      for (const d of deps) {
        for (const l of entryLeaves[d] ?? []) {
          set.add(l);
        }
      }
      if (inst.tag !== null) {
        set.add(inst.tag);
      }
      leaves = [...set].sort();
    }
    const dedupKey = `${s}\u0000${pi}\u0000${leaves.join(",")}`;
    if (dedup.has(dedupKey)) {
      return;
    }
    const live = phase === 1 || (obsCodes[s] === FALSE && deps.every((d) => entryLive[d] === true));
    if (live ? liveCodes[pi][s] !== TRUE : recCodes[pi][s] !== TRUE) {
      throw new Error(
        `Π(Σ): internal error, a derivation of (${boundaryOf(s)}, ${inst.p}, ${itemKey(itemOf(s))}) disagrees with the well-founded model.`,
      );
    }
    if (entries.length >= MAX_PROVENANCE_ENTRIES) {
      throw new Error(
        `Π(Σ): more than ${MAX_PROVENANCE_ENTRIES} witnessing entries; the kernel reports this instead of truncating them.`,
      );
    }
    dedup.add(dedupKey);
    const index = entries.length;
    const entryId = `e${index + 1}`;
    const item = itemOf(s);
    const provenance: Provenance =
      inst.origin === "base"
        ? { kind: "base", baseId: inst.baseId ?? "" }
        : inst.origin === "structural"
          ? { kind: "structural", rule: inst.structural ?? "bottom-excl" }
          : inst.coverCells !== null
            ? {
                kind: "derived",
                rule: inst.rule,
                depEntryIds: deps.map((d) => entries[d]?.entryId ?? ""),
                baseLeaves: leaves,
                coverCells: inst.coverCells,
              }
            : {
                kind: "derived",
                rule: inst.rule,
                depEntryIds: deps.map((d) => entries[d]?.entryId ?? ""),
                baseLeaves: leaves,
              };
    entries.push({
      entryId,
      boundary: boundaryOf(s),
      polarity: inst.p,
      item,
      key: itemKey(item),
      provenance,
    });
    entryLeaves.push(leaves);
    entryLive.push(live);
    const k = s * 2 + pi;
    (allByKey[k] ??= []).push(index);
    if (live) {
      (liveByKey[k] ??= []).push(index);
    }
    fresh.push(index);
  };

  /** Derive entries from one instance with the current entries (phase 1: Live only). */
  const tryInstance = (inst: Instance, phase: 1 | 2): void => {
    if (phase === 1 && obsCodes[inst.slot] !== FALSE) {
      return;
    }
    const lists: (readonly number[])[] = [];
    for (const pr of inst.prems) {
      const c = candidates(pr, phase);
      if (c.length === 0) {
        return;
      }
      lists.push(inst.firstOnly ? c.slice(0, 1) : c);
    }
    for (const alternatives of inst.choices) {
      let chosen: number[] | undefined;
      for (const alt of alternatives) {
        const picks: number[] = [];
        for (const pr of alt) {
          const first = candidates(pr, phase)[0];
          if (first === undefined) {
            break;
          }
          picks.push(first);
        }
        if (picks.length === alt.length) {
          chosen = picks;
          break;
        }
      }
      if (chosen === undefined) {
        return;
      }
      for (const e of chosen) {
        lists.push([e]);
      }
    }
    // Every combination of witnessing entries (one per premise).
    const positions = new Array<number>(lists.length).fill(0);
    for (;;) {
      addEntry(
        inst,
        lists.map((l, j) => l[positions[j] ?? 0] ?? 0),
        phase,
      );
      let j = lists.length - 1;
      while (j >= 0) {
        const next = (positions[j] ?? 0) + 1;
        if (next < (lists[j]?.length ?? 0)) {
          positions[j] = next;
          break;
        }
        positions[j] = 0;
        j -= 1;
      }
      if (j < 0) {
        break;
      }
    }
  };

  const runPhase = (phase: 1 | 2): void => {
    let dirty: number[] = instances.map((_, i) => i);
    const mark = new Uint8Array(instances.length);
    while (dirty.length > 0) {
      fresh.length = 0;
      for (const i of dirty) {
        const inst = instances[i];
        if (inst !== undefined) {
          tryInstance(inst, phase);
        }
      }
      mark.fill(0);
      const next: number[] = [];
      for (const e of fresh) {
        const entry = entries[e];
        if (entry === undefined) {
          continue;
        }
        const s = slotOf(bIndex.get(entry.boundary) ?? 0, uIndex.get(entry.key) ?? 0);
        for (const i of instancesByPrem[s * 2 + polIndex(entry.polarity)] ?? []) {
          if (mark[i] === 0) {
            mark[i] = 1;
            next.push(i);
          }
        }
      }
      dirty = next;
    }
  };
  runPhase(1);
  runPhase(2);

  // Every true rec atom has a witnessing entry and every true live atom a Live one.
  for (let s = 0; s < nS; s++) {
    for (const pi of [0, 1] as const) {
      const k = s * 2 + pi;
      if ((recCodes[pi][s] === TRUE) !== ((allByKey[k]?.length ?? 0) > 0)) {
        throw new Error(
          `Π(Σ): internal error, the records of (${boundaryOf(s)}, ${pi === 0 ? "+" : "-"}, ${itemKey(itemOf(s))}) lack witnesses.`,
        );
      }
      if ((liveCodes[pi][s] === TRUE) !== ((liveByKey[k]?.length ?? 0) > 0)) {
        throw new Error(
          `Π(Σ): internal error, the authority of (${boundaryOf(s)}, ${pi === 0 ? "+" : "-"}, ${itemKey(itemOf(s))}) lacks a Live witness.`,
        );
      }
    }
  }

  const liveEntryIds = new Set<string>();
  entries.forEach((e, i) => {
    if (entryLive[i] === true) {
      liveEntryIds.add(e.entryId);
    }
  });

  return {
    boundaries,
    universe,
    rec: recCodes,
    live: liveCodes,
    coll: collCodes,
    obs: obsCodes,
    entries,
    liveEntryIds,
  };
}

export function andAll(items: readonly Item[]): Item {
  if (items.length === 0) {
    throw new Error("andAll requires at least one item.");
  }
  const first = items[0];
  if (first === undefined) {
    throw new Error("Unexpected empty array.");
  }
  return items.slice(1).reduce((acc, cur) => and(acc, cur), first);
}

export function orAll(items: readonly Item[]): Item {
  if (items.length === 0) {
    throw new Error("orAll requires at least one item.");
  }
  const first = items[0];
  if (first === undefined) {
    throw new Error("Unexpected empty array.");
  }
  return items.slice(1).reduce((acc, cur) => or(acc, cur), first);
}
