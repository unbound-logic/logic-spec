/**
 * Boundary meet-semilattice (B, ⊑, ⊓, ⊤_B, ⊥_B), finitary Grothendieck covers,
 * native relation scoping, and handle individuation (I_B) for UL-Core.
 *
 * Implements spec/core.md §2 items 4-6.
 */

export const TOP_BOUNDARY = "⊤_B";
export const BOT_BOUNDARY = "⊥_B";

/**
 * The meet of two boundaries in the open-world reading of the registry (core.md §2 item 4): known
 * to be a non-empty boundary, known to be ⊥_B, or unknown because nothing registered settles it.
 */
export type MeetStatus =
  | { readonly kind: "overlap"; readonly meet: string }
  | { readonly kind: "disjoint" }
  | { readonly kind: "unknown" };

/** A cover registered by WitnessCover, with the identifier Withdraw names it by (core.md §2 item 7). */
export type RegisteredCover = {
  readonly id: string;
  readonly target: string;
  readonly cells: readonly string[];
};

/**
 * Validity of a registered cover {B_i} ▷ B against the current boundary system (core.md §2 item 5):
 * invalid when some non-empty B' ⊑ B is disjoint from every cell; unverified when no such B' exists
 * but some non-empty B' ⊑ B is known to overlap no cell and has an unknown overlap with one. The
 * witnesses are those sub-boundaries B'.
 */
export type CoverValidity =
  | { readonly kind: "valid" }
  | { readonly kind: "invalid"; readonly witnesses: readonly string[] }
  | { readonly kind: "unverified"; readonly witnesses: readonly string[] };

export type CoverOptions = {
  /** Seed only valid registered covers, leaving out unverified ones as well as invalid ones. */
  readonly verifiedOnly?: boolean;
};

export type HandleSpec = {
  readonly id: string;
  readonly criterion: string;
  readonly kind: "structural" | "contingent";
};

export type BoundaryConfig = {
  readonly parents?: readonly string[];
  readonly nativeRelations?: readonly string[];
  readonly handles?: readonly HandleSpec[];
  readonly handleFilter?: (handle: HandleSpec) => boolean;
};

function pairKey(a: string, b: string): string {
  return a < b ? `${a}\0${b}` : `${b}\0${a}`;
}

/** Largest cover the transitivity closure of witnessedCoversOf enumerates. */
const MAX_COVER_CELLS = 16;

function coverSignature(cells: readonly string[]): string {
  return [...cells].sort().join("\0");
}

/**
 * Manages the bounded meet-semilattice of Domain Boundaries, finitary
 * exhaustive covers, and boundary-scoped handle admissibility.
 */
export class BoundarySystem {
  readonly #defined = new Set<string>([TOP_BOUNDARY, BOT_BOUNDARY]);
  readonly #parents = new Map<string, Set<string>>();
  readonly #disjointPairs = new Set<string>();
  readonly #explicitMeets = new Map<string, string>();
  readonly #nativeRelations = new Map<string, Set<string>>();
  readonly #handles = new Map<string, Map<string, HandleSpec>>();
  readonly #registeredCovers = new Map<string, RegisteredCover>();
  #coverCounter = 0;

  constructor() {
    this.#parents.set(TOP_BOUNDARY, new Set());
    this.#parents.set(BOT_BOUNDARY, new Set());
    this.#nativeRelations.set(TOP_BOUNDARY, new Set());
    this.#nativeRelations.set(BOT_BOUNDARY, new Set());
    this.#handles.set(TOP_BOUNDARY, new Map());
    this.#handles.set(BOT_BOUNDARY, new Map());
  }

  /** Create a deep independent snapshot copy of the current BoundarySystem. */
  clone(): BoundarySystem {
    const copy = new BoundarySystem();
    copy.#defined.clear();
    for (const id of this.#defined) {
      copy.#defined.add(id);
    }
    copy.#parents.clear();
    for (const [id, ps] of this.#parents) {
      copy.#parents.set(id, new Set(ps));
    }
    copy.#disjointPairs.clear();
    for (const dp of this.#disjointPairs) {
      copy.#disjointPairs.add(dp);
    }
    copy.#explicitMeets.clear();
    for (const [k, m] of this.#explicitMeets) {
      copy.#explicitMeets.set(k, m);
    }
    copy.#nativeRelations.clear();
    for (const [id, rels] of this.#nativeRelations) {
      copy.#nativeRelations.set(id, new Set(rels));
    }
    copy.#handles.clear();
    for (const [id, hm] of this.#handles) {
      copy.#handles.set(id, new Map(hm));
    }
    copy.#registeredCovers.clear();
    for (const [id, cover] of this.#registeredCovers) {
      copy.#registeredCovers.set(id, { id, target: cover.target, cells: [...cover.cells] });
    }
    copy.#coverCounter = this.#coverCounter;
    return copy;
  }

  /** Register a new Domain Boundary into the semilattice. */
  defineBoundary(id: string, config: BoundaryConfig = {}): void {
    if (id === TOP_BOUNDARY || id === BOT_BOUNDARY) {
      throw new Error(`Cannot redefine reserved boundary "${id}".`);
    }
    if (this.#defined.has(id)) {
      throw new Error(`Boundary "${id}" is already defined.`);
    }
    const parentList = config.parents ?? [TOP_BOUNDARY];
    for (const p of parentList) {
      this.#assertDefined(p);
    }
    for (let i = 0; i < parentList.length; i++) {
      const pi = parentList[i];
      if (pi === undefined) {
        continue;
      }
      if (pi === BOT_BOUNDARY) {
        throw new Error(`Non-empty boundary "${id}" cannot have "${BOT_BOUNDARY}" as a parent.`);
      }
      for (let j = i + 1; j < parentList.length; j++) {
        const pj = parentList[j];
        if (pj !== undefined && this.#hasDisjointAncestors(pi, pj)) {
          throw new Error(
            `Cannot define non-empty boundary "${id}" under disjoint parents "${pi}" and "${pj}".`,
          );
        }
      }
    }

    const rels = new Set<string>(config.nativeRelations ?? []);
    for (const p of parentList) {
      const parentRels = this.#nativeRelations.get(p);
      if (parentRels !== undefined) {
        for (const r of parentRels) {
          rels.add(r);
        }
      }
    }

    const handleMap = new Map<string, HandleSpec>();
    if (config.handles !== undefined) {
      for (const h of config.handles) {
        handleMap.set(h.id, h);
      }
    } else {
      // Default: the handles common to every declared parent (core.md §2 item 6), so a
      // boundary with several parents admits only individuals all of them admit.
      const declaredParents = parentList.filter((p) => p !== TOP_BOUNDARY);
      const [first, ...rest] = declaredParents.map((p) => this.#handles.get(p) ?? new Map<string, HandleSpec>());
      for (const [hid, spec] of first ?? new Map<string, HandleSpec>()) {
        if (
          rest.every((other) => other.has(hid)) &&
          (config.handleFilter === undefined || config.handleFilter(spec))
        ) {
          handleMap.set(hid, spec);
        }
      }
    }

    // Domain monotonicity (core.md §2 item 6): Dom(D') ⊆ Dom(D) whenever D' ⊑ D. ⊤_B carries
    // no handle registry, so only declared parents constrain the sub-boundary.
    for (const p of parentList) {
      if (p === TOP_BOUNDARY) {
        continue;
      }
      const parentHandles = this.#handles.get(p);
      for (const hid of handleMap.keys()) {
        if (parentHandles?.has(hid) !== true) {
          throw new Error(
            `Domain monotonicity violation: handle "${hid}" of "${id}" is not in Dom("${p}"); a sub-boundary's handles must be a subset of every parent's handles.`,
          );
        }
      }
    }

    this.#defined.add(id);
    this.#parents.set(id, new Set(parentList));
    this.#nativeRelations.set(id, rels);
    this.#handles.set(id, handleMap);
  }

  /** Declare two boundaries disjoint (a ⊓ b = ⊥_B). */
  declareDisjoint(a: string, b: string): void {
    this.#assertDefined(a);
    this.#assertDefined(b);
    this.#assertCanBeDisjoint(a, b);
    this.#disjointPairs.add(pairKey(a, b));
  }

  /** Explicitly register the meet boundary (a ⊓ b = meetId). */
  defineMeet(a: string, b: string, meetId: string): void {
    this.#assertDefined(a);
    this.#assertDefined(b);
    this.#assertDefined(meetId);
    if (!this.refines(meetId, a) || !this.refines(meetId, b)) {
      throw new Error(`Meet "${meetId}" must refine both "${a}" and "${b}".`);
    }
    if (meetId === BOT_BOUNDARY) {
      this.#assertCanBeDisjoint(a, b);
      if (a !== BOT_BOUNDARY && b !== BOT_BOUNDARY) {
        this.#disjointPairs.add(pairKey(a, b));
      }
    } else if (this.#hasDisjointAncestors(a, b)) {
      throw new Error(
        `Cannot register non-empty meet "${meetId}" for disjoint boundaries "${a}" and "${b}".`,
      );
    }
    this.#explicitMeets.set(pairKey(a, b), meetId);
  }

  #assertCanBeDisjoint(a: string, b: string): void {
    if (a === b && a !== BOT_BOUNDARY) {
      throw new Error(`Non-empty boundary "${a}" cannot be disjoint from itself.`);
    }
    if (a === BOT_BOUNDARY || b === BOT_BOUNDARY) {
      return;
    }
    if (this.refines(a, b) || this.refines(b, a)) {
      throw new Error(`Cannot declare "${a}" and "${b}" disjoint because one refines the other.`);
    }
    const explicitMeet = this.#explicitMeets.get(pairKey(a, b));
    if (explicitMeet !== undefined && explicitMeet !== BOT_BOUNDARY) {
      throw new Error(
        `Cannot declare "${a}" and "${b}" disjoint: explicit non-empty meet "${explicitMeet}" is registered.`,
      );
    }
    const common = [...this.#defined].filter(
      (c) => c !== BOT_BOUNDARY && this.refines(c, a) && this.refines(c, b),
    );
    if (common.length > 0) {
      throw new Error(
        `Cannot declare "${a}" and "${b}" disjoint: common non-empty sub-boundaries [${common.join(", ")}] exist.`,
      );
    }
  }

  /** Test refinement partial order: sub ⊑ sup. */
  refines(sub: string, sup: string): boolean {
    this.#assertDefined(sub);
    this.#assertDefined(sup);
    if (sub === BOT_BOUNDARY || sup === TOP_BOUNDARY || sub === sup) {
      return true;
    }
    if (sup === BOT_BOUNDARY || sub === TOP_BOUNDARY) {
      return false;
    }
    const visited = new Set<string>();
    const stack = [sub];
    while (stack.length > 0) {
      const cur = stack.pop();
      if (cur === undefined || visited.has(cur)) {
        continue;
      }
      visited.add(cur);
      if (cur === sup) {
        return true;
      }
      const ps = this.#parents.get(cur);
      if (ps !== undefined) {
        for (const p of ps) {
          stack.push(p);
        }
      }
    }
    return false;
  }

  /**
   * The meet of a and b in the open-world reading of the registry (core.md §2 item 4): an overlap
   * when one refines the other, a meet is registered, or a unique maximal common sub-boundary is
   * registered; disjoint when ⊥_B is involved or disjointness is declared for them or inherited
   * from declared ancestors; unknown otherwise. Several maximal common sub-boundaries throw.
   */
  meetStatus(a: string, b: string): MeetStatus {
    this.#assertDefined(a);
    this.#assertDefined(b);
    if (a === BOT_BOUNDARY || b === BOT_BOUNDARY) {
      return { kind: "disjoint" };
    }
    if (this.refines(a, b)) {
      return { kind: "overlap", meet: a };
    }
    if (this.refines(b, a)) {
      return { kind: "overlap", meet: b };
    }

    const explicit = this.#explicitMeets.get(pairKey(a, b));
    if (explicit !== undefined) {
      return explicit === BOT_BOUNDARY ? { kind: "disjoint" } : { kind: "overlap", meet: explicit };
    }

    // Disjoint if either pair or any pair of ancestors is declared disjoint.
    for (const x of this.#ancestorsOf(a)) {
      for (const y of this.#ancestorsOf(b)) {
        if (this.#disjointPairs.has(pairKey(x, y))) {
          return { kind: "disjoint" };
        }
      }
    }

    const common = [...this.#defined].filter(
      (c) => c !== BOT_BOUNDARY && this.refines(c, a) && this.refines(c, b),
    );
    if (common.length === 0) {
      return { kind: "unknown" };
    }
    const maximal = common.filter(
      (c) => !common.some((other) => other !== c && this.refines(c, other)),
    );
    if (maximal.length === 1 && maximal[0] !== undefined) {
      return { kind: "overlap", meet: maximal[0] };
    }
    throw new Error(
      `Ambiguous meet for "${a}" and "${b}": candidates [${maximal.join(", ")}]; call defineMeet() or declareDisjoint().`,
    );
  }

  /**
   * Greatest lower bound a ⊓ b: the known meet, or ⊥_B when the boundaries are disjoint. An unknown
   * overlap has no meet to return and throws; callers that can meet one use meetStatus.
   */
  meet(a: string, b: string): string {
    const status = this.meetStatus(a, b);
    if (status.kind === "unknown") {
      throw new Error(
        `Unknown meet for "${a}" and "${b}": nothing registered settles their overlap; call defineMeet() or declareDisjoint().`,
      );
    }
    return status.kind === "overlap" ? status.meet : BOT_BOUNDARY;
  }

  /** True iff a and b are known to overlap (a ⊓ b is a known non-empty boundary). */
  overlaps(a: string, b: string): boolean {
    return this.meetStatus(a, b).kind === "overlap";
  }

  /** All defined non-empty boundaries refined by b (including b itself when b ≠ ⊥_B). */
  nonEmptySubBoundaries(b: string): readonly string[] {
    this.#assertDefined(b);
    if (b === BOT_BOUNDARY) {
      return [];
    }
    return [...this.#defined].filter((x) => x !== BOT_BOUNDARY && this.refines(x, b));
  }

  /** All defined non-empty boundaries (excluding ⊤_B only if requested). */
  nonEmptyBoundaries(): readonly string[] {
    return [...this.#defined].filter((x) => x !== BOT_BOUNDARY);
  }

  /** True when b is non-empty and admits no strictly smaller non-empty sub-boundary. */
  isAtomic(b: string): boolean {
    this.#assertDefined(b);
    return b !== BOT_BOUNDARY && this.nonEmptySubBoundaries(b).length === 1;
  }

  /**
   * Register a witnessed finite exhaustive cover {B_i} ▷ target under the identifier `id` (a fresh
   * one when omitted) and return it. Enforces Axiom 1 (Refinement) and Axiom 5 (Non-Vacuity); a
   * cover that later structure refutes stays registered, and coverValidity reports it.
   */
  registerCover(target: string, cells: readonly string[], id?: string): string {
    this.#assertDefined(target);
    for (const c of cells) {
      this.#assertDefined(c);
      if (!this.refines(c, target)) {
        throw new Error(`Cover Refinement violation: cell "${c}" does not refine "${target}".`);
      }
    }
    const nonEmptyCells = [...new Set(cells.filter((c) => c !== BOT_BOUNDARY))];
    if (target !== BOT_BOUNDARY && nonEmptyCells.length === 0) {
      throw new Error(
        `Cover Non-Vacuity violation: empty cover cannot cover non-empty boundary "${target}".`,
      );
    }
    let coverId = id;
    if (coverId === undefined) {
      do {
        this.#coverCounter += 1;
        coverId = `cover${this.#coverCounter}`;
      } while (this.#registeredCovers.has(coverId));
    } else if (this.#registeredCovers.has(coverId)) {
      throw new Error(`Cover identifier "${coverId}" is already registered.`);
    }
    this.#registeredCovers.set(coverId, { id: coverId, target, cells: nonEmptyCells });
    return coverId;
  }

  /** Withdraw(c) for a cover: remove the registered cover `id`; false when none is registered. */
  withdrawCover(id: string): boolean {
    return this.#registeredCovers.delete(id);
  }

  /** The covers registered by WitnessCover and not withdrawn, in registration order. */
  registeredCovers(): readonly RegisteredCover[] {
    return [...this.#registeredCovers.values()].map((c) => ({ ...c, cells: [...c.cells] }));
  }

  /** Validity of the registered cover `id` against the current boundary system (item 5). */
  coverValidity(id: string): CoverValidity {
    const cover = this.#registeredCovers.get(id);
    if (cover === undefined) {
      throw new Error(`No registered cover "${id}".`);
    }
    return this.#assessCover(cover.target, cover.cells);
  }

  #assessCover(target: string, cells: readonly string[]): CoverValidity {
    if (target === BOT_BOUNDARY) {
      return { kind: "valid" };
    }
    const invalid: string[] = [];
    const unverified: string[] = [];
    for (const sub of this.nonEmptySubBoundaries(target)) {
      const statuses = cells.map((c) => this.meetStatus(c, sub));
      if (statuses.some((st) => st.kind === "overlap")) {
        continue;
      }
      (statuses.every((st) => st.kind === "disjoint") ? invalid : unverified).push(sub);
    }
    if (invalid.length > 0) {
      return { kind: "invalid", witnesses: invalid };
    }
    return unverified.length > 0 ? { kind: "unverified", witnesses: unverified } : { kind: "valid" };
  }

  /**
   * Enumerate all finitary witnessed covers {B_i} ▷ target generated by the
   * 5 coverage axioms (Refinement, Identity, Meet-Stability, Transitivity, Non-Vacuity)
   * from the registered covers that are not invalid (item 5); with `verifiedOnly`, from the
   * valid ones alone.
   */
  witnessedCoversOf(target: string, options: CoverOptions = {}): readonly (readonly string[])[] {
    this.#assertDefined(target);
    if (target === BOT_BOUNDARY) {
      return [[]];
    }

    // The witnessed covers (item 5): the registered covers that are not invalid (with verifiedOnly,
    // the valid ones), closed under Identity, Meet-Stability and Transitivity (Axioms 2–4). A
    // derived cover is judged by the same rule as a registered one and is not derived when it fails
    // it, so no witnessed cover is invalid and no base change comes out empty.
    const covers = new Map<string, Map<string, readonly string[]>>();
    const rejected = new Map<string, Set<string>>();
    for (const b of this.nonEmptyBoundaries()) {
      covers.set(b, new Map([[coverSignature([b]), [b]]]));
      rejected.set(b, new Set());
    }
    const admit = (b: string, cells: readonly string[]): boolean => {
      const bCovers = covers.get(b);
      const bRejected = rejected.get(b);
      if (bCovers === undefined || bRejected === undefined) {
        return false;
      }
      const sig = coverSignature(cells);
      if (bCovers.has(sig) || bRejected.has(sig)) {
        return false;
      }
      if (cells.length > MAX_COVER_CELLS) {
        throw new Error(
          `Cover closure for "${b}" needs a cover of ${cells.length} cells, above the limit of ${MAX_COVER_CELLS}; refusing to truncate the witnessed covers.`,
        );
      }
      const validity = this.#assessCover(b, cells).kind;
      if (validity === "invalid" || (validity === "unverified" && options.verifiedOnly === true)) {
        bRejected.add(sig);
        return false;
      }
      bCovers.set(sig, cells);
      return true;
    };
    for (const { target: sup, cells } of this.#registeredCovers.values()) {
      if (sup !== BOT_BOUNDARY) {
        admit(sup, cells);
      }
    }

    // The pass bound and the cell cap are resource limits, not semantics: where either would cut
    // the closure short, report it (item 14, G6).
    const baseChanged = new Set<string>();
    const maxPasses = 2 * this.#defined.size + 2;
    let converged = false;
    for (let pass = 0; pass <= maxPasses; pass++) {
      let changed = false;
      for (const b of this.nonEmptyBoundaries()) {
        const bCovers = covers.get(b);
        if (bCovers === undefined) {
          continue;
        }
        for (const cover of [...bCovers.values()]) {
          // Axiom 4 (Transitivity): replace one cell by a witnessed cover of that cell.
          for (let idx = 0; idx < cover.length; idx++) {
            const cell = cover[idx];
            const cellCovers = cell === undefined ? undefined : covers.get(cell);
            if (cellCovers === undefined) {
              continue;
            }
            for (const subCover of [...cellCovers.values()]) {
              if (subCover.length === 1 && subCover[0] === cell) {
                continue;
              }
              const expanded = [
                ...new Set([...cover.slice(0, idx), ...subCover, ...cover.slice(idx + 1)]),
              ];
              if (admit(b, expanded)) {
                changed = true;
              }
            }
          }
          // Axiom 3 (Meet-Stability), once per cover: the base change to every non-empty B' ⊑ b. A
          // cell whose overlap with B' is unknown may hold part of B', so it blocks the base change.
          const key = `${b}\0${coverSignature(cover)}`;
          if (baseChanged.has(key) || (cover.length === 1 && cover[0] === b)) {
            continue;
          }
          baseChanged.add(key);
          for (const sub of this.nonEmptySubBoundaries(b)) {
            if (sub === b) {
              continue;
            }
            const statuses = cover.map((c) => this.meetStatus(c, sub));
            if (statuses.some((st) => st.kind === "unknown")) {
              continue;
            }
            const pulled = [
              ...new Set(statuses.flatMap((st) => (st.kind === "overlap" ? [st.meet] : []))),
            ];
            if (pulled.length === 0) {
              throw new Error(
                `Cover closure derived ∅ ▷ "${sub}" from a cover of "${b}" that is not invalid, which Axiom 5 forbids.`,
              );
            }
            if (admit(sub, pulled)) {
              changed = true;
            }
          }
        }
      }
      if (!changed) {
        converged = true;
        break;
      }
    }
    if (!converged) {
      throw new Error(
        `Cover closure did not converge within ${maxPasses + 1} passes; refusing to truncate the witnessed covers.`,
      );
    }

    return [...(covers.get(target)?.values() ?? [])];
  }

  /** Check whether `cells` constitutes a witnessed exhaustive cover of `target`. */
  isWitnessedCover(target: string, cells: readonly string[], options: CoverOptions = {}): boolean {
    this.#assertDefined(target);
    for (const c of cells) {
      this.#assertDefined(c);
    }
    const normalized = [...new Set(cells.filter((c) => c !== BOT_BOUNDARY))];
    if (target === BOT_BOUNDARY) {
      return normalized.length === 0;
    }
    if (normalized.length === 0) {
      return false;
    }
    const sig = coverSignature(normalized);
    return this.witnessedCoversOf(target, options).some((c) => coverSignature(c) === sig);
  }

  /** Return all handles in Dom(boundary). */
  handlesOf(boundary: string): readonly HandleSpec[] {
    this.#assertDefined(boundary);
    return [...(this.#handles.get(boundary)?.values() ?? [])];
  }

  /** Look up handle specification in Dom(boundary). */
  getHandle(boundary: string, handleId: string): HandleSpec | undefined {
    this.#assertDefined(boundary);
    return this.#handles.get(boundary)?.get(handleId);
  }

  /** Verify whether handleId ∈ Dom(boundary) and matches individuation criterion I_B if given. */
  isAdmissibleHandle(boundary: string, handleId: string, suppliedCriterion?: string): boolean {
    const spec = this.getHandle(boundary, handleId);
    if (spec === undefined) {
      return false;
    }
    if (suppliedCriterion !== undefined && spec.criterion !== suppliedCriterion) {
      return false;
    }
    return true;
  }

  /** Return true iff `relation` is native to `boundary`. */
  hasNativeRelation(boundary: string, relation: string): boolean {
    this.#assertDefined(boundary);
    return this.#nativeRelations.get(boundary)?.has(relation) ?? false;
  }

  #assertDefined(boundary: string): void {
    if (!this.#defined.has(boundary)) {
      throw new Error(`Unknown boundary "${boundary}".`);
    }
  }

  #hasDisjointAncestors(a: string, b: string): boolean {
    for (const x of this.#ancestorsOf(a)) {
      for (const y of this.#ancestorsOf(b)) {
        if (this.#disjointPairs.has(pairKey(x, y))) {
          return true;
        }
      }
    }
    return false;
  }

  #ancestorsOf(b: string): Set<string> {
    const res = new Set<string>();
    const stack = [b];
    while (stack.length > 0) {
      const cur = stack.pop();
      if (cur === undefined || res.has(cur)) {
        continue;
      }
      res.add(cur);
      const ps = this.#parents.get(cur);
      if (ps !== undefined) {
        for (const p of ps) {
          stack.push(p);
        }
      }
    }
    return res;
  }
}
