/**
 * Boundary meet-semilattice (B, ⊑, ⊓, ⊤_B, ⊥_B), finitary Grothendieck covers,
 * native relation scoping, and handle individuation (I_B) for UL-Core.
 *
 * Implements spec/core.md §2 items 4-6.
 */

export const TOP_BOUNDARY = "⊤_B";
export const BOT_BOUNDARY = "⊥_B";

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
  readonly #registeredCovers = new Map<string, string[][]>();

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
    for (const [target, coverList] of this.#registeredCovers) {
      copy.#registeredCovers.set(
        target,
        coverList.map((cells) => [...cells]),
      );
    }
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

    this.#defined.add(id);
    this.#parents.set(id, new Set(parentList));

    const rels = new Set<string>(config.nativeRelations ?? []);
    for (const p of parentList) {
      const parentRels = this.#nativeRelations.get(p);
      if (parentRels !== undefined) {
        for (const r of parentRels) {
          rels.add(r);
        }
      }
    }
    this.#nativeRelations.set(id, rels);

    const handleMap = new Map<string, HandleSpec>();
    if (config.handles !== undefined) {
      for (const h of config.handles) {
        handleMap.set(h.id, h);
      }
    } else {
      for (const p of parentList) {
        const parentHandles = this.#handles.get(p);
        if (parentHandles === undefined) {
          continue;
        }
        for (const [hid, spec] of parentHandles) {
          if (config.handleFilter === undefined || config.handleFilter(spec)) {
            handleMap.set(hid, spec);
          }
        }
      }
    }
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

  /** Compute greatest lower bound a ⊓ b in the boundary meet-semilattice. */
  meet(a: string, b: string): string {
    this.#assertDefined(a);
    this.#assertDefined(b);
    if (a === BOT_BOUNDARY || b === BOT_BOUNDARY) {
      return BOT_BOUNDARY;
    }
    if (this.refines(a, b)) {
      return a;
    }
    if (this.refines(b, a)) {
      return b;
    }

    const explicit = this.#explicitMeets.get(pairKey(a, b));
    if (explicit !== undefined) {
      return explicit;
    }

    // Disjoint if either pair or any pair of ancestors is declared disjoint.
    for (const x of this.#ancestorsOf(a)) {
      for (const y of this.#ancestorsOf(b)) {
        if (this.#disjointPairs.has(pairKey(x, y))) {
          return BOT_BOUNDARY;
        }
      }
    }

    const common = [...this.#defined].filter(
      (c) => c !== BOT_BOUNDARY && this.refines(c, a) && this.refines(c, b),
    );
    if (common.length === 0) {
      return BOT_BOUNDARY;
    }
    const maximal = common.filter(
      (c) => !common.some((other) => other !== c && this.refines(c, other)),
    );
    if (maximal.length === 1 && maximal[0] !== undefined) {
      return maximal[0];
    }
    throw new Error(
      `Ambiguous meet for "${a}" and "${b}": candidates [${maximal.join(", ")}]; call defineMeet() or declareDisjoint().`,
    );
  }

  /** Return true iff a ⊓ b ≠ ⊥_B. */
  overlaps(a: string, b: string): boolean {
    return this.meet(a, b) !== BOT_BOUNDARY;
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
   * Register a witnessed finite exhaustive cover {B_i} ▷ target.
   * Enforces Axiom 1 (Refinement) and Axiom 5 (Non-Vacuity).
   */
  registerCover(target: string, cells: readonly string[]): void {
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
    const existing = this.#registeredCovers.get(target) ?? [];
    existing.push(nonEmptyCells);
    this.#registeredCovers.set(target, existing);
  }

  /**
   * Enumerate all finitary witnessed covers {B_i} ▷ target generated by the
   * 5 coverage axioms (Refinement, Identity, Meet-Stability, Transitivity, Non-Vacuity).
   */
  witnessedCoversOf(target: string): readonly (readonly string[])[] {
    this.#assertDefined(target);
    if (target === BOT_BOUNDARY) {
      return [[]];
    }

    const baseCovers = new Map<string, Map<string, readonly string[]>>();
    for (const b of this.nonEmptyBoundaries()) {
      const m = new Map<string, readonly string[]>();
      const id = [b];
      m.set(coverSignature(id), id);
      baseCovers.set(b, m);
    }

    // Seed registered covers and their Meet-Stability pullbacks (Axioms 1, 2, 3, 5).
    for (const [sup, coverList] of this.#registeredCovers) {
      for (const cells of coverList) {
        if (sup === BOT_BOUNDARY) {
          continue;
        }
        for (const sub of this.nonEmptySubBoundaries(sup)) {
          const pulled = [
            ...new Set(cells.map((c) => this.meet(c, sub)).filter((m) => m !== BOT_BOUNDARY)),
          ];
          if (pulled.length > 0) {
            baseCovers.get(sub)?.set(coverSignature(pulled), pulled);
          }
        }
      }
    }

    // Close under finite Transitivity (Axiom 4) up to a bounded iteration depth.
    const maxPasses = this.#defined.size + 1;
    for (let pass = 0; pass < maxPasses; pass++) {
      let changed = false;
      for (const b of this.nonEmptyBoundaries()) {
        const bCovers = baseCovers.get(b);
        if (bCovers === undefined) {
          continue;
        }
        for (const cover of [...bCovers.values()]) {
          for (let idx = 0; idx < cover.length; idx++) {
            const cell = cover[idx];
            if (cell === undefined) {
              continue;
            }
            const cellCovers = baseCovers.get(cell);
            if (cellCovers === undefined) {
              continue;
            }
            for (const subCover of cellCovers.values()) {
              const expanded = [
                ...new Set([...cover.slice(0, idx), ...subCover, ...cover.slice(idx + 1)]),
              ];
              if (expanded.length === 0 || expanded.length > 16) {
                continue;
              }
              const sig = coverSignature(expanded);
              if (!bCovers.has(sig)) {
                bCovers.set(sig, expanded);
                changed = true;
              }
            }
          }
        }
      }
      if (!changed) {
        break;
      }
    }

    return [...(baseCovers.get(target)?.values() ?? [])];
  }

  /** Check whether `cells` constitutes a witnessed exhaustive cover of `target`. */
  isWitnessedCover(target: string, cells: readonly string[]): boolean {
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
    return this.witnessedCoversOf(target).some((c) => coverSignature(c) === sig);
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
