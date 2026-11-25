/**
 * Dual-polarity semantics, well-founded DAG provenance, Inference Quarantine,
 * Scoped Cut, vertical inquiry transitions (Observe/Retract/RefineBoundary),
 * and M1/M2 anti-immunization laws for UL-Core.
 *
 * Implements spec/core.md §2 item 7 and §3 items 8-12.
 */

import { BOT_BOUNDARY, BoundarySystem } from "./boundary.ts";
import {
  and,
  bottom,
  collectHandles,
  collectRelations,
  computeItemLevel,
  flip,
  itemKey,
  or,
  substituteHandle,
  type Item,
  type Polarity,
} from "./syntax.ts";

export type DerivedStatus = "Open" | "Grounded" | "Excluded" | "Collision";

export type Provenance =
  | { readonly kind: "base"; readonly baseId: string }
  | { readonly kind: "structural"; readonly rule: "bottom-excl" | "struct-imposs" | "refl-eval" }
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

export type IncompatibilityConstraint = {
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
      readonly originalStatusBefore: DerivedStatus;
      readonly originalExcludedPreserved: boolean;
    }
  | {
      readonly ok: false;
      readonly violation:
        | "M1-circular"
        | "M1-contingent-excision"
        | "M1-unwitnessed-proxy"
        | "M2-not-refuted";
      readonly reason: string;
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

/** Snapshot of all derived grounds, collisions, obstructions, and Live statuses at current Σ. */
export class EvaluationSnapshot {
  readonly #entriesById = new Map<string, GroundEntry>();
  readonly #bySlot = new Map<string, GroundEntry[]>();
  readonly #collisions = new Set<string>();
  readonly #obstructed = new Set<string>();
  readonly #liveIds = new Set<string>();

  constructor(
    entries: readonly GroundEntry[],
    collisions: ReadonlySet<string>,
    obstructed: ReadonlySet<string>,
    liveIds: ReadonlySet<string>,
  ) {
    for (const e of entries) {
      this.#entriesById.set(e.entryId, e);
      const slot = slotKey(e.boundary, e.polarity, e.key);
      const list = this.#bySlot.get(slot) ?? [];
      list.push(e);
      this.#bySlot.set(slot, list);
    }
    for (const c of collisions) {
      this.#collisions.add(c);
    }
    for (const o of obstructed) {
      this.#obstructed.add(o);
    }
    for (const id of liveIds) {
      this.#liveIds.add(id);
    }
  }

  /** Derived status of (boundary, item) in Σ. */
  statusOf(boundary: string, item: Item): DerivedStatus {
    const key = itemKey(item);
    const hasPos = (this.#bySlot.get(slotKey(boundary, "+", key))?.length ?? 0) > 0;
    const hasNeg = (this.#bySlot.get(slotKey(boundary, "-", key))?.length ?? 0) > 0;
    if (hasPos && hasNeg) {
      return "Collision";
    }
    if (hasPos) {
      return "Grounded";
    }
    if (hasNeg) {
      return "Excluded";
    }
    return "Open";
  }

  /** Return all entries (Live or quarantined) for (boundary, polarity, item). */
  allGrounds(boundary: string, polarity: Polarity, item: Item): readonly GroundEntry[] {
    return this.#bySlot.get(slotKey(boundary, polarity, itemKey(item))) ?? [];
  }

  /** Return only Live (unobstructed, well-founded, unquarantined) grounds. */
  liveGrounds(boundary: string, polarity: Polarity, item: Item): readonly GroundEntry[] {
    return this.allGrounds(boundary, polarity, item).filter((e) => this.#liveIds.has(e.entryId));
  }

  /** Return true iff (boundary, polarity, item) has at least one Live ground. */
  isLive(boundary: string, polarity: Polarity, item: Item): boolean {
    return this.liveGrounds(boundary, polarity, item).length > 0;
  }

  /** Return true iff a specific entryId is Live. */
  isEntryLive(entryId: string): boolean {
    return this.#liveIds.has(entryId);
  }

  /** Return true iff (boundary, item) is in local Collision. */
  isCollided(boundary: string, item: Item): boolean {
    return this.#collisions.has(`${boundary}\0${itemKey(item)}`);
  }

  /** Return true iff (boundary, item) is obstructed by a collision on itself or a sub-boundary. */
  isObstructed(boundary: string, item: Item): boolean {
    return this.#obstructed.has(`${boundary}\0${itemKey(item)}`);
  }

  /** Open revision obligations corresponding to all local collisions. */
  revisionObligations(): readonly RevisionObligation[] {
    const out: RevisionObligation[] = [];
    for (const c of this.#collisions) {
      const sep = c.indexOf("\0");
      if (sep >= 0) {
        out.push({ boundary: c.slice(0, sep), itemKey: c.slice(sep + 1) });
      }
    }
    return out;
  }

  /** True iff No-Gluts holds globally across the evaluated state. */
  isCollisionFree(): boolean {
    return this.#collisions.size === 0;
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
};

type StageRecord = {
  readonly stage: number;
  readonly baseObservations: ReadonlyMap<string, BaseObservation>;
  readonly theorems: ReadonlyMap<string, RecordedTheorem>;
  readonly incompatibilities: readonly IncompatibilityConstraint[];
  readonly structuralCollapses: readonly { readonly boundary: string; readonly item: Item }[];
  readonly trackedItems: ReadonlyMap<string, Item>;
};

/**
 * Stateful vertical inquiry engine managing Σ = (G+, G-, C_B, O_rev) and
 * computing horizontal dual-polarity derivations under Quarantine & Scoped Cut.
 */
export class InquiryEngine {
  readonly boundaries: BoundarySystem;
  readonly monotoneOnly: boolean;
  readonly #baseObservations = new Map<string, BaseObservation>();
  readonly #theorems = new Map<string, RecordedTheorem>();
  readonly #incompatibilities: IncompatibilityConstraint[] = [];
  readonly #structuralCollapses: { readonly boundary: string; readonly item: Item }[] = [];
  readonly #trackedItems = new Map<string, Item>();
  readonly #stageArchive = new Map<number, StageRecord>();
  readonly #history: string[] = [];
  #stage = 0;

  constructor(boundaries: BoundarySystem, options: EngineOptions = {}) {
    this.boundaries = boundaries;
    this.monotoneOnly = options.monotoneOnly ?? false;
    this.#trackItem(bottom());
    this.#captureStage();
  }

  get stage(): number {
    return this.#stage;
  }

  get transitionLog(): readonly string[] {
    return this.#history;
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
  ): void {
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
    this.#trackItem(item);
    for (const dep of requiredGrounds) {
      this.#trackItem(dep.item);
    }
    this.#theorems.set(theoremId, {
      theoremId,
      boundary,
      polarity,
      item,
      requiredBaseIds: [...requiredBaseIds],
      requiredGrounds: [...requiredGrounds],
    });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Theorem${polarity}(${boundary}, ${itemKey(item)}, ${theoremId})`);
    this.#captureStage();
  }

  /** Collect every handle identifier mentioned anywhere in Σ or registered boundaries. */
  mentionedHandles(): ReadonlySet<string> {
    const out = new Set<string>();
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

  /** Register material incompatibility constraint A ⊥_B C in C_B. */
  addIncompatibility(boundary: string, left: Item, right: Item): void {
    if (boundary === BOT_BOUNDARY) {
      throw new Error(`Cannot add material incompatibility on "${BOT_BOUNDARY}".`);
    }
    this.boundaries.nonEmptySubBoundaries(boundary);
    this.#trackItem(left);
    this.#trackItem(right);
    this.#incompatibilities.push({ boundary, left, right });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Constrain(${itemKey(left)} ⊥_${boundary} ${itemKey(right)})`);
    this.#captureStage();
  }

  /** Register structural boundary collapse B ⊓ [A] = ⊥_B, inducing +(A → ⊥) and -A. */
  addStructuralCollapse(boundary: string, item: Item): void {
    if (boundary === BOT_BOUNDARY) {
      throw new Error(`Cannot add structural collapse on "${BOT_BOUNDARY}".`);
    }
    this.boundaries.nonEmptySubBoundaries(boundary);
    this.#trackItem(item);
    this.#structuralCollapses.push({ boundary, item });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Collapse(${boundary} ⊓ [${itemKey(item)}] = ⊥_B)`);
    this.#captureStage();
  }

  /**
   * Attempt RefineBoundary(fromBoundary -> toBoundary) obeying M1 + M2.
   * Rejects circular predicates (M1(i)) and bare contingent handle excisions (M1(ii)),
   * and verifies that M2 preserves Excluded (-) on (fromBoundary, originalUniversal).
   */
  refineBoundary(req: M1RefinementRequest): M1Result {
    if (
      req.toBoundary === BOT_BOUNDARY ||
      !this.boundaries.refines(req.toBoundary, req.fromBoundary)
    ) {
      throw new Error(
        `Invalid refinement: "${req.toBoundary}" must be a non-empty sub-boundary of "${req.fromBoundary}".`,
      );
    }

    const beforeSnap = this.evaluate([req.originalUniversal]);
    const statusBefore = beforeSnap.statusOf(req.fromBoundary, req.originalUniversal);
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
    // non-refuted surviving handle u in toBoundary where δ(u) carries a Live (+ or -) witness.
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
      const hasIndependentLiveWitness = survivingHandles.some((h) => {
        if (req.originalUniversal.kind === "forall") {
          const targetInstance = substituteHandle(
            req.originalUniversal.body,
            req.originalUniversal.variable,
            h.id,
          );
          const targetStatus = critSnap.statusOf(req.fromBoundary, targetInstance);
          if (targetStatus === "Excluded" || targetStatus === "Collision") {
            return false;
          }
        }
        const critInstance = substituteHandle(req.criterionItem, critVar, h.id);
        return (
          critSnap.isLive(req.fromBoundary, "+", critInstance) ||
          critSnap.isLive(req.fromBoundary, "-", critInstance)
        );
      });
      if (!hasIndependentLiveWitness) {
        return {
          ok: false,
          violation: "M1-unwitnessed-proxy",
          reason: `M1(iii) violation: splitting criterion lacks an independent Live witness on a non-refuted surviving handle of "${req.toBoundary}".`,
        };
      }
    }

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

  /** Compute full evaluation fixpoint over current Σ and optional extra query items. */
  evaluate(extraItems: readonly Item[] = []): EvaluationSnapshot {
    const currentRecord = this.#stageArchive.get(this.#stage);
    if (currentRecord === undefined) {
      throw new Error(`Missing archived inquiry stage ${this.#stage}.`);
    }
    return this.#evaluateRecord(currentRecord, extraItems);
  }

  /** Evaluate the frozen historical inquiry state at `stage` (0 <= stage <= current stage). */
  evaluateAtStage(stage: number, extraItems: readonly Item[] = []): EvaluationSnapshot {
    if (!Number.isInteger(stage) || stage < 0 || stage > this.#stage) {
      throw new Error(`Invalid stage ${stage}; expected integer in [0, ${this.#stage}].`);
    }
    const record = this.#stageArchive.get(stage);
    if (record === undefined) {
      throw new Error(`Missing archived inquiry stage ${stage}.`);
    }
    return this.#evaluateRecord(record, extraItems);
  }

  #evaluateRecord(
    record: StageRecord,
    extraItems: readonly Item[] = [],
  ): EvaluationSnapshot {
    const universe = new Map<string, Item>();
    const enqueueItem = (it: Item): void => {
      const k = itemKey(it);
      if (universe.has(k)) {
        return;
      }
      universe.set(k, it);
      for (const sub of directSubItems(it)) {
        enqueueItem(sub);
      }
      if (it.kind === "forall" || it.kind === "exists") {
        for (const h of this.boundaries.handlesOf(it.domain)) {
          enqueueItem(substituteHandle(it.body, it.variable, h.id));
        }
      }
    };
    for (const it of [...record.trackedItems.values(), ...extraItems]) {
      enqueueItem(it);
    }

    const reflectionEvaluations: { readonly item: Item; readonly polarity: Polarity }[] = [];
    for (const it of universe.values()) {
      if (it.kind !== "refl" || it.targetStage === undefined) {
        continue;
      }
      if (!Number.isInteger(it.targetStage) || it.targetStage < 0 || it.targetStage >= record.stage) {
        continue;
      }
      if (!Number.isInteger(it.reflectedLevel) || it.reflectedLevel < computeItemLevel(it.targetItem)) {
        continue;
      }
      if (!this.#isDefinedNonEmptyBoundary(it.targetBoundary)) {
        continue;
      }
      const priorRecord = this.#stageArchive.get(it.targetStage);
      if (priorRecord === undefined) {
        continue;
      }
      const priorSnap = this.#evaluateRecord(priorRecord, [it.targetItem]);
      const holds =
        it.targetStatus !== undefined
          ? priorSnap.statusOf(it.targetBoundary, it.targetItem) === it.targetStatus
          : priorSnap.isLive(it.targetBoundary, it.targetPolarity, it.targetItem);
      reflectionEvaluations.push({ item: it, polarity: holds ? "+" : "-" });
    }

    const provenanceBaseLeaves = (prov: Provenance): readonly string[] => {
      if (prov.kind === "base") {
        return [prov.baseId];
      }
      if (prov.kind === "structural") {
        return [`@${prov.rule}`];
      }
      return prov.baseLeaves;
    };

    const nonEmptyB = this.boundaries.nonEmptyBoundaries();
    const bot = bottom();

    type ClosurePassResult = {
      readonly entries: GroundEntry[];
      readonly collisions: Set<string>;
      readonly obstructed: Set<string>;
      readonly liveIds: Set<string>;
    };

    type LockedConflictEntry = {
      readonly boundary: string;
      readonly polarity: Polarity;
      readonly item: Item;
      readonly rule: string;
      readonly baseLeaves: readonly string[];
      readonly coverCells?: readonly string[];
    };

    const runClosure = (
      blockedSlots: ReadonlySet<string>,
      lockedConflictEntries: readonly LockedConflictEntry[] = [],
    ): ClosurePassResult => {
      const entries: GroundEntry[] = [];
      const byEntryId = new Map<string, GroundEntry>();
      const lockedEntryIds = new Set<string>();
      const dedupKeys = new Set<string>();
      let seq = 0;

      const addEntry = (
        boundary: string,
        polarity: Polarity,
        item: Item,
        provenance: Provenance,
      ): GroundEntry | undefined => {
        if (boundary === BOT_BOUNDARY) {
          return undefined;
        }
        const key = itemKey(item);
        const leaves = provenanceBaseLeaves(provenance);
        const dedup = `${boundary}\0${polarity}\0${key}\0${leaves.join(",")}`;
        if (dedupKeys.has(dedup)) {
          return undefined;
        }
        dedupKeys.add(dedup);
        seq += 1;
        const entryId = `e${seq}`;
        const entry: GroundEntry = { entryId, boundary, polarity, item, key, provenance };
        entries.push(entry);
        byEntryId.set(entryId, entry);
        return entry;
      };

      const mergeLeaves = (depIds: readonly string[], extraTag?: string): readonly string[] => {
        const set = new Set<string>();
        for (const id of depIds) {
          const dep = byEntryId.get(id);
          if (dep !== undefined) {
            for (const l of provenanceBaseLeaves(dep.provenance)) {
              set.add(l);
            }
          }
        }
        if (extraTag !== undefined) {
          set.add(extraTag);
        }
        return [...set].sort();
      };

      const makeDerived = (
        rule: string,
        depEntryIds: readonly string[],
        extraTag?: string,
        coverCells?: readonly string[],
      ): Provenance => {
        const baseLeaves = mergeLeaves(depEntryIds, extraTag);
        return coverCells !== undefined
          ? { kind: "derived", rule, depEntryIds, baseLeaves, coverCells }
          : { kind: "derived", rule, depEntryIds, baseLeaves };
      };

      // 1. Seed base observations, locked symmetric-conflict witnesses, structural exclusions, and cross-stage reflections.
      const baseEntryIdByBaseId = new Map<string, string>();
      for (const obs of record.baseObservations.values()) {
        const created = addEntry(obs.boundary, obs.polarity, obs.item, {
          kind: "base",
          baseId: obs.baseId,
        });
        if (created !== undefined) {
          baseEntryIdByBaseId.set(obs.baseId, created.entryId);
        }
      }
      for (const lc of lockedConflictEntries) {
        const prov: Provenance =
          lc.coverCells !== undefined
            ? {
                kind: "derived",
                rule: lc.rule,
                depEntryIds: [],
                baseLeaves: lc.baseLeaves,
                coverCells: lc.coverCells,
              }
            : { kind: "derived", rule: lc.rule, depEntryIds: [], baseLeaves: lc.baseLeaves };
        const created = addEntry(lc.boundary, lc.polarity, lc.item, prov);
        if (created !== undefined) {
          lockedEntryIds.add(created.entryId);
        }
      }
      for (const b of nonEmptyB) {
        addEntry(b, "-", bot, { kind: "structural", rule: "bottom-excl" });
      }
      for (const reflRes of reflectionEvaluations) {
        for (const b of nonEmptyB) {
          addEntry(b, reflRes.polarity, reflRes.item, {
            kind: "structural",
            rule: "refl-eval",
          });
        }
      }
      for (const sc of record.structuralCollapses) {
        addEntry(
          sc.boundary,
          "+",
          { kind: "implies", antecedent: sc.item, consequent: bot },
          { kind: "structural", rule: "struct-imposs" },
        );
        addEntry(sc.boundary, "-", sc.item, {
          kind: "structural",
          rule: "struct-imposs",
        });
      }

      const computeAuthorized = (disallowedSlots: ReadonlySet<string>): Set<string> => {
        const auth = new Set<string>();
        let changed = true;
        while (changed) {
          changed = false;
          for (const e of entries) {
            if (auth.has(e.entryId)) {
              continue;
            }
            if (lockedEntryIds.has(e.entryId)) {
              continue;
            }
            if (disallowedSlots.has(`${e.boundary}\0${e.key}`)) {
              continue;
            }
            if (e.provenance.kind !== "derived") {
              auth.add(e.entryId);
              changed = true;
              continue;
            }
            if (e.provenance.depEntryIds.every((id) => auth.has(id))) {
              auth.add(e.entryId);
              changed = true;
            }
          }
        }
        return auth;
      };

      const computeStatusState = (): {
        collisions: Set<string>;
        obstructed: Set<string>;
        liveIds: Set<string>;
      } => {
        const posPairs = new Set<string>();
        const negPairs = new Set<string>();
        for (const e of entries) {
          const pk = `${e.boundary}\0${e.key}`;
          if (e.polarity === "+") {
            posPairs.add(pk);
          } else {
            negPairs.add(pk);
          }
        }
        const collisions = new Set<string>();
        for (const pk of posPairs) {
          if (negPairs.has(pk)) {
            collisions.add(pk);
          }
        }
        const obstructed = new Set<string>();
        for (const c of collisions) {
          const sep = c.indexOf("\0");
          const colB = c.slice(0, sep);
          const colKey = c.slice(sep + 1);
          for (const b of nonEmptyB) {
            if (this.boundaries.refines(colB, b)) {
              obstructed.add(`${b}\0${colKey}`);
            }
          }
        }
        const liveIds = computeAuthorized(obstructed);
        return { collisions, obstructed, liveIds };
      };

      // 2. Fixpoint closure over all UL-Core rules gated against definitively obstructed slots.
      for (let iter = 0; iter < 64; iter++) {
        const beforeCount = entries.length;
        const authorizedIds = computeAuthorized(blockedSlots);
        const snapshotList = [...entries];

        // A) Symmetric downward heredity (for both + and -)
        for (const e of snapshotList) {
          for (const sub of this.boundaries.nonEmptySubBoundaries(e.boundary)) {
            if (sub !== e.boundary) {
              addEntry(sub, e.polarity, e.item, makeDerived("down", [e.entryId]));
            }
          }
        }

        // B) Strong polarity flip ~A (valid on polarities; Live depends on source)
        for (const e of snapshotList) {
          const oppPol: Polarity = e.polarity === "+" ? "-" : "+";
          const flipped = flip(e.item);
          if (universe.has(itemKey(flipped))) {
            addEntry(e.boundary, oppPol, flipped, makeDerived("flip", [e.entryId]));
          }
          if (e.item.kind === "flip") {
            addEntry(e.boundary, oppPol, e.item.inner, makeDerived("flip-elim", [e.entryId]));
          }
        }

        // Index helpers on current entries for rule joins
        const entriesByBPolKey = new Map<string, GroundEntry[]>();
        const liveByBPolKey = new Map<string, GroundEntry[]>();
        for (const e of entries) {
          const k = slotKey(e.boundary, e.polarity, e.key);
          const allList = entriesByBPolKey.get(k) ?? [];
          allList.push(e);
          entriesByBPolKey.set(k, allList);
          if (authorizedIds.has(e.entryId)) {
            const lList = liveByBPolKey.get(k) ?? [];
            lList.push(e);
            liveByBPolKey.set(k, lList);
          }
        }

        // C) Local exclusion rules (no false transmission needed) & Live-gated transmission rules
        for (const it of universe.values()) {
          const k = itemKey(it);
          for (const b of nonEmptyB) {
            if (it.kind === "implies") {
              const antK = itemKey(it.antecedent);
              const conK = itemKey(it.consequent);
              const posAnt = entriesByBPolKey.get(slotKey(b, "+", antK)) ?? [];
              const negCon = entriesByBPolKey.get(slotKey(b, "-", conK)) ?? [];
              for (const pa of posAnt) {
                for (const nc of negCon) {
                  addEntry(
                    b,
                    "-",
                    it,
                    makeDerived("counter-implies", [pa.entryId, nc.entryId]),
                  );
                }
              }
            } else if (it.kind === "and") {
              const lk = itemKey(it.left);
              const rk = itemKey(it.right);
              for (const nl of entriesByBPolKey.get(slotKey(b, "-", lk)) ?? []) {
                addEntry(b, "-", it, makeDerived("and-excl-l", [nl.entryId]));
              }
              for (const nr of entriesByBPolKey.get(slotKey(b, "-", rk)) ?? []) {
                addEntry(b, "-", it, makeDerived("and-excl-r", [nr.entryId]));
              }
              const liveL = liveByBPolKey.get(slotKey(b, "+", lk)) ?? [];
              const liveR = liveByBPolKey.get(slotKey(b, "+", rk)) ?? [];
              for (const ll of liveL) {
                for (const lr of liveR) {
                  addEntry(b, "+", it, makeDerived("and-intro", [ll.entryId, lr.entryId]));
                }
              }
              for (const lp of liveByBPolKey.get(slotKey(b, "+", k)) ?? []) {
                addEntry(b, "+", it.left, makeDerived("and-elim-l", [lp.entryId]));
                addEntry(b, "+", it.right, makeDerived("and-elim-r", [lp.entryId]));
              }
            } else if (it.kind === "or") {
              const lk = itemKey(it.left);
              const rk = itemKey(it.right);
              for (const nl of entriesByBPolKey.get(slotKey(b, "-", lk)) ?? []) {
                for (const nr of entriesByBPolKey.get(slotKey(b, "-", rk)) ?? []) {
                  addEntry(b, "-", it, makeDerived("or-excl", [nl.entryId, nr.entryId]));
                }
              }
              // D2: Cover-Witnessed Disjunction across finitary witnessed covers of b
              for (const cover of this.boundaries.witnessedCoversOf(b)) {
                const cellDeps: string[] = [];
                let covered = true;
                for (const cell of cover) {
                  const cellPos =
                    liveByBPolKey.get(slotKey(cell, "+", lk))?.[0] ??
                    liveByBPolKey.get(slotKey(cell, "+", rk))?.[0];
                  if (cellPos === undefined) {
                    covered = false;
                    break;
                  }
                  cellDeps.push(cellPos.entryId);
                }
                if (covered && cellDeps.length > 0) {
                  addEntry(b, "+", it, makeDerived("or-cover", cellDeps, undefined, cover));
                }
              }
            } else if (it.kind === "forall") {
              const handles = this.boundaries.handlesOf(it.domain);
              for (const h of handles) {
                const instK = itemKey(substituteHandle(it.body, it.variable, h.id));
                for (const negInst of entriesByBPolKey.get(slotKey(b, "-", instK)) ?? []) {
                  addEntry(b, "-", it, makeDerived("forall-counter", [negInst.entryId]));
                }
              }
              if (handles.length > 0) {
                const allDeps: string[] = [];
                let allOk = true;
                for (const h of handles) {
                  const instK = itemKey(substituteHandle(it.body, it.variable, h.id));
                  const liveInst = liveByBPolKey.get(slotKey(b, "+", instK))?.[0];
                  if (liveInst === undefined) {
                    allOk = false;
                    break;
                  }
                  allDeps.push(liveInst.entryId);
                }
                if (allOk) {
                  addEntry(b, "+", it, makeDerived("forall-generic", allDeps));
                }
              }
            } else if (it.kind === "exists") {
              const handles = this.boundaries.handlesOf(it.domain);
              for (const h of handles) {
                const instK = itemKey(substituteHandle(it.body, it.variable, h.id));
                for (const posInst of entriesByBPolKey.get(slotKey(b, "+", instK)) ?? []) {
                  addEntry(b, "+", it, makeDerived("exists-intro", [posInst.entryId]));
                }
              }
              if (handles.length > 0) {
                const allNegDeps: string[] = [];
                let allNeg = true;
                for (const h of handles) {
                  const instK = itemKey(substituteHandle(it.body, it.variable, h.id));
                  const negInst = liveByBPolKey.get(slotKey(b, "-", instK))?.[0];
                  if (negInst === undefined) {
                    allNeg = false;
                    break;
                  }
                  allNegDeps.push(negInst.entryId);
                }
                if (allNeg) {
                  addEntry(b, "-", it, makeDerived("exists-excl", allNegDeps));
                }
              }
            }
          }
        }

        // D) Scoped Cut / Modus Ponens across Live antecedents and Live conditionals on overlapping meets
        const liveImplies = entries.filter(
          (e) => e.polarity === "+" && e.item.kind === "implies" && authorizedIds.has(e.entryId),
        );
        const liveAll = entries.filter((e) => authorizedIds.has(e.entryId));
        for (const imp of liveImplies) {
          if (imp.item.kind !== "implies") {
            continue;
          }
          const antK = itemKey(imp.item.antecedent);
          for (const ant of liveAll) {
            if (ant.polarity !== "+" || ant.key !== antK) {
              continue;
            }
            const meetB = this.boundaries.meet(ant.boundary, imp.boundary);
            if (meetB !== BOT_BOUNDARY) {
              addEntry(
                meetB,
                "+",
                imp.item.consequent,
                makeDerived("mp", [ant.entryId, imp.entryId]),
              );
            }
          }
        }

        // E) Cover Gluing (∨E): Live +(A ∨ C), Live +(A → E), Live +(C → E) => +E
        for (const orEntry of liveAll) {
          if (orEntry.polarity !== "+" || orEntry.item.kind !== "or") {
            continue;
          }
          const leftK = itemKey(orEntry.item.left);
          const rightK = itemKey(orEntry.item.right);
          for (const impA of liveImplies) {
            if (impA.boundary !== orEntry.boundary || impA.item.kind !== "implies") {
              continue;
            }
            if (itemKey(impA.item.antecedent) !== leftK) {
              continue;
            }
            const targetE = impA.item.consequent;
            const targetEK = itemKey(targetE);
            for (const impC of liveImplies) {
              if (impC.boundary !== orEntry.boundary || impC.item.kind !== "implies") {
                continue;
              }
              if (
                itemKey(impC.item.antecedent) === rightK &&
                itemKey(impC.item.consequent) === targetEK
              ) {
                addEntry(
                  orEntry.boundary,
                  "+",
                  targetE,
                  makeDerived("or-elim", [orEntry.entryId, impA.entryId, impC.entryId]),
                );
              }
            }
          }
        }

        // F) Material Incompatibility (A ⊥_B C) triggered only by Live grounds
        for (const inc of record.incompatibilities) {
          const lk = itemKey(inc.left);
          const rk = itemKey(inc.right);
          for (const b of this.boundaries.nonEmptySubBoundaries(inc.boundary)) {
            for (const la of liveByBPolKey.get(slotKey(b, "+", lk)) ?? []) {
              addEntry(
                b,
                "-",
                inc.right,
                makeDerived("incompat", [la.entryId], `@incompat:${lk}⊥${rk}`),
              );
            }
            for (const ra of liveByBPolKey.get(slotKey(b, "+", rk)) ?? []) {
              addEntry(
                b,
                "-",
                inc.left,
                makeDerived("incompat", [ra.entryId], `@incompat:${lk}⊥${rk}`),
              );
            }
          }
        }

        // F2) Admit verified theorems once their required base leaves and Live ground dependencies exist
        for (const thm of record.theorems.values()) {
          const depIdSet = new Set<string>();
          let allSatisfied = true;
          for (const reqId of thm.requiredBaseIds) {
            const entryId = baseEntryIdByBaseId.get(reqId);
            if (entryId === undefined) {
              allSatisfied = false;
              break;
            }
            depIdSet.add(entryId);
          }
          if (!allSatisfied) {
            continue;
          }
          for (const dep of thm.requiredGrounds) {
            const liveDep = liveByBPolKey.get(
              slotKey(dep.boundary, dep.polarity, itemKey(dep.item)),
            )?.[0];
            if (liveDep === undefined) {
              allSatisfied = false;
              break;
            }
            depIdSet.add(liveDep.entryId);
          }
          if (allSatisfied) {
            addEntry(
              thm.boundary,
              thm.polarity,
              thm.item,
              makeDerived("theorem", [...depIdSet], `@thm:${thm.theoremId}`),
            );
          }
        }

        // G) Boundary-Scoped Congruence ≈_B (native relations only!)
        for (const eq of liveAll) {
          if (eq.polarity !== "+" || eq.item.kind !== "equiv") {
            continue;
          }
          const eqB = eq.item.boundary;
          if (!this.boundaries.refines(eq.boundary, eqB) && eq.boundary !== eqB) {
            continue;
          }
          for (const target of liveAll) {
            if (target.boundary !== eq.boundary || target.item.kind !== "atom") {
              continue;
            }
            if (!this.boundaries.hasNativeRelation(eqB, target.item.relation)) {
              continue;
            }
            const leftVal = eq.item.left;
            const rightVal = eq.item.right;
            if (target.item.roles.some((r) => r.handle === leftVal)) {
              const rewritten: Item = {
                kind: "atom",
                relation: target.item.relation,
                roles: target.item.roles.map((r) =>
                  r.handle === leftVal ? { role: r.role, handle: rightVal } : r,
                ),
              };
              addEntry(
                target.boundary,
                target.polarity,
                rewritten,
                makeDerived("congruence", [eq.entryId, target.entryId]),
              );
            }
            if (target.item.roles.some((r) => r.handle === rightVal)) {
              const rewrittenRev: Item = {
                kind: "atom",
                relation: target.item.relation,
                roles: target.item.roles.map((r) =>
                  r.handle === rightVal ? { role: r.role, handle: leftVal } : r,
                ),
              };
              addEntry(
                target.boundary,
                target.polarity,
                rewrittenRev,
                makeDerived("congruence", [eq.entryId, target.entryId]),
              );
            }
          }
        }

        // H) Structural Impossibility Exclusion: Live +(A → ⊥) induces -A without enabling DNE
        for (const imp of liveImplies) {
          if (imp.item.kind === "implies" && imp.item.consequent.kind === "bottom") {
            addEntry(
              imp.boundary,
              "-",
              imp.item.antecedent,
              makeDerived("imposs-excl", [imp.entryId]),
            );
          }
        }

        // I) Standalone Cover-Gluing (Sheaf Gluing): ∀cell ∈ cover. cell ⊩± E [Live] => B ⊩± E
        for (const it of universe.values()) {
          const ik = itemKey(it);
          for (const b of nonEmptyB) {
            for (const cover of this.boundaries.witnessedCoversOf(b)) {
              if (cover.length === 1 && cover[0] === b) {
                continue;
              }
              for (const pol of ["+", "-"] as const) {
                const cellDeps: string[] = [];
                let allCovered = true;
                for (const cell of cover) {
                  const cellEntry = liveByBPolKey.get(slotKey(cell, pol, ik))?.[0];
                  if (cellEntry === undefined) {
                    allCovered = false;
                    break;
                  }
                  cellDeps.push(cellEntry.entryId);
                }
                if (allCovered && cellDeps.length > 0) {
                  addEntry(b, pol, it, makeDerived("cover-glue", cellDeps, undefined, cover));
                }
              }
            }
          }
        }

        if (entries.length === beforeCount) {
          break;
        }
      }

      const state = computeStatusState();
      return {
        entries,
        collisions: state.collisions,
        obstructed: state.obstructed,
        liveIds: state.liveIds,
      };
    };

    // Van Gelder alternating fixpoint + source-SCC locking of symmetric conflicts prevents
    // ghost collisions from both defeated branches and mutual incompatibility cycles.
    const extraBlocked = new Set<string>();
    const lockedEntriesMap = new Map<string, LockedConflictEntry>();
    let finalPass: ClosurePassResult | undefined;

    for (let outer = 0; outer < 32; outer++) {
      const lockedList = [...lockedEntriesMap.values()];
      let defObstructed = new Set<string>(extraBlocked);
      let mayPass = runClosure(defObstructed, lockedList);
      for (let round = 0; round < 32; round++) {
        mayPass = runClosure(defObstructed, lockedList);
        const defInput = new Set<string>(mayPass.obstructed);
        for (const s of extraBlocked) {
          defInput.add(s);
        }
        const defPass = runClosure(defInput, lockedList);
        const nextDef = new Set<string>(defPass.obstructed);
        for (const s of extraBlocked) {
          nextDef.add(s);
        }
        if (
          nextDef.size === defObstructed.size &&
          [...nextDef].every((s) => defObstructed.has(s))
        ) {
          break;
        }
        defObstructed = nextDef;
      }
      finalPass = mayPass;

      const unresolved = new Set<string>();
      for (const s of mayPass.obstructed) {
        if (!defObstructed.has(s)) {
          unresolved.add(s);
        }
      }
      if (unresolved.size === 0) {
        break;
      }

      const entryMap = new Map<string, GroundEntry>();
      for (const e of mayPass.entries) {
        entryMap.set(e.entryId, e);
      }
      const adj = new Map<string, Set<string>>();
      for (const s of unresolved) {
        adj.set(s, new Set<string>());
      }

      const collectAncestorSlotsInU = (startEntry: GroundEntry): Set<string> => {
        const found = new Set<string>();
        const seen = new Set<string>();
        const stack: string[] = [];
        if (startEntry.provenance.kind === "derived") {
          for (const d of startEntry.provenance.depEntryIds) {
            stack.push(d);
          }
        }
        while (stack.length > 0) {
          const curId = stack.pop();
          if (curId === undefined || seen.has(curId)) {
            continue;
          }
          seen.add(curId);
          const anc = entryMap.get(curId);
          if (anc === undefined) {
            continue;
          }
          const ancSlot = `${anc.boundary}\0${anc.key}`;
          if (unresolved.has(ancSlot)) {
            found.add(ancSlot);
          }
          if (anc.provenance.kind === "derived") {
            for (const nextId of anc.provenance.depEntryIds) {
              stack.push(nextId);
            }
          }
        }
        return found;
      };

      for (const e of mayPass.entries) {
        const s = `${e.boundary}\0${e.key}`;
        if (!unresolved.has(s)) {
          continue;
        }
        for (const u of collectAncestorSlotsInU(e)) {
          if (u !== s) {
            adj.get(u)?.add(s);
          }
        }
      }

      for (const s of unresolved) {
        if (mayPass.collisions.has(s)) {
          continue;
        }
        const sep = s.indexOf("\0");
        const b = s.slice(0, sep);
        const k = s.slice(sep + 1);
        for (const sSub of unresolved) {
          const subSep = sSub.indexOf("\0");
          const bSub = sSub.slice(0, subSep);
          const kSub = sSub.slice(subSep + 1);
          if (kSub === k && bSub !== b && this.boundaries.refines(bSub, b)) {
            adj.get(sSub)?.add(s);
          }
        }
      }

      const sccs = computeSourceSCCs(unresolved, adj);
      let addedLock = false;
      for (const sourceScc of sccs) {
        for (const s of sourceScc) {
          if (!extraBlocked.has(s)) {
            extraBlocked.add(s);
            addedLock = true;
          }
          for (const e of mayPass.entries) {
            if (`${e.boundary}\0${e.key}` === s && e.provenance.kind === "derived") {
              const lk = `${e.boundary}\0${e.polarity}\0${e.key}\0${e.provenance.baseLeaves.join(",")}`;
              if (!lockedEntriesMap.has(lk)) {
                lockedEntriesMap.set(lk, {
                  boundary: e.boundary,
                  polarity: e.polarity,
                  item: e.item,
                  rule: e.provenance.rule,
                  baseLeaves: e.provenance.baseLeaves,
                  ...(e.provenance.coverCells !== undefined
                    ? { coverCells: e.provenance.coverCells }
                    : {}),
                });
              }
            }
          }
        }
      }
      if (!addedLock) {
        break;
      }
    }

    if (finalPass === undefined) {
      finalPass = runClosure(extraBlocked, [...lockedEntriesMap.values()]);
    }

    return new EvaluationSnapshot(
      finalPass.entries,
      finalPass.collisions,
      finalPass.obstructed,
      finalPass.liveIds,
    );
  }

  #addBaseObservation(
    boundary: string,
    polarity: Polarity,
    item: Item,
    baseId: string,
    handleAuth?: HandleAuth,
  ): void {
    this.boundaries.nonEmptySubBoundaries(boundary);
    if (handleAuth !== undefined) {
      if (!this.boundaries.isAdmissibleHandle(boundary, handleAuth.handle, handleAuth.criterion)) {
        throw new Error(
          `Anti-Equivocation violation: handle "${handleAuth.handle}" with criterion "${handleAuth.criterion}" is not admissible in "${boundary}".`,
        );
      }
    }
    this.#trackItem(item);
    const key = itemKey(item);
    this.#baseObservations.set(baseId, { baseId, boundary, polarity, item, key });
    this.#stage += 1;
    this.#history.push(`Σ${this.#stage}:Observe${polarity}(${boundary}, ${key}, ${baseId})`);
    this.#captureStage();
  }

  #isDefinedNonEmptyBoundary(boundary: string): boolean {
    if (boundary === BOT_BOUNDARY) {
      return false;
    }
    try {
      return this.boundaries.refines(boundary, boundary);
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
      trackedItems: new Map(this.#trackedItems),
    });
  }

  #trackItem(item: Item): void {
    const k = itemKey(item);
    if (this.#trackedItems.has(k)) {
      return;
    }
    this.#trackedItems.set(k, item);
    for (const sub of directSubItems(item)) {
      this.#trackItem(sub);
    }
  }
}

function slotKey(boundary: string, polarity: Polarity, key: string): string {
  return `${boundary}\0${polarity}\0${key}`;
}

/** Tarjan strongly connected components restricted to those with zero external incoming edges. */
function computeSourceSCCs(
  nodes: ReadonlySet<string>,
  adj: ReadonlyMap<string, ReadonlySet<string>>,
): readonly (readonly string[])[] {
  let index = 0;
  const indices = new Map<string, number>();
  const lowlink = new Map<string, number>();
  const onStack = new Set<string>();
  const stack: string[] = [];
  const sccs: string[][] = [];

  const strongConnect = (v: string): void => {
    indices.set(v, index);
    lowlink.set(v, index);
    index += 1;
    stack.push(v);
    onStack.add(v);

    for (const w of adj.get(v) ?? []) {
      if (!nodes.has(w)) {
        continue;
      }
      if (!indices.has(w)) {
        strongConnect(w);
        lowlink.set(v, Math.min(lowlink.get(v) ?? 0, lowlink.get(w) ?? 0));
      } else if (onStack.has(w)) {
        lowlink.set(v, Math.min(lowlink.get(v) ?? 0, indices.get(w) ?? 0));
      }
    }

    if (lowlink.get(v) === indices.get(v)) {
      const comp: string[] = [];
      while (stack.length > 0) {
        const w = stack.pop();
        if (w === undefined) {
          break;
        }
        onStack.delete(w);
        comp.push(w);
        if (w === v) {
          break;
        }
      }
      sccs.push(comp);
    }
  };

  for (const n of nodes) {
    if (!indices.has(n)) {
      strongConnect(n);
    }
  }

  const sccOf = new Map<string, number>();
  for (let i = 0; i < sccs.length; i++) {
    for (const n of sccs[i] ?? []) {
      sccOf.set(n, i);
    }
  }
  const hasExternalIncoming = new Array<boolean>(sccs.length).fill(false);
  for (const [u, outs] of adj) {
    const su = sccOf.get(u);
    if (su === undefined) {
      continue;
    }
    for (const v of outs) {
      const sv = sccOf.get(v);
      if (sv !== undefined && sv !== su) {
        hasExternalIncoming[sv] = true;
      }
    }
  }

  const sources: (readonly string[])[] = [];
  for (let i = 0; i < sccs.length; i++) {
    const comp = sccs[i];
    if (comp !== undefined && !hasExternalIncoming[i]) {
      sources.push(comp);
    }
  }
  return sources;
}

function directSubItems(item: Item): readonly Item[] {
  switch (item.kind) {
    case "atom":
    case "bottom":
    case "equiv":
    case "ref":
      return [];
    case "flip":
      return [item.inner];
    case "and":
    case "or":
      return [item.left, item.right];
    case "implies":
      return [item.antecedent, item.consequent];
    case "forall":
    case "exists":
      return item.domainConstraint !== undefined
        ? [item.body, item.domainConstraint]
        : [item.body];
    case "refl":
      return [item.targetItem];
  }
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
