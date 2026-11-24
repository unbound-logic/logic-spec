/**
 * Syntax, role-indexed atomic grammar (G3), and Curry Paradox firewall
 * (Stratified Reflection + Strict Positivity) for UL-Core.
 *
 * Implements spec/core.md §1 items 1-3.
 */

export type RoleArg = {
  readonly role: string;
  readonly handle: string;
};

export type Polarity = "+" | "-";

export type Item =
  | { readonly kind: "atom"; readonly relation: string; readonly roles: readonly RoleArg[] }
  | { readonly kind: "bottom" }
  | { readonly kind: "equiv"; readonly boundary: string; readonly left: string; readonly right: string }
  | { readonly kind: "flip"; readonly inner: Item }
  | { readonly kind: "and"; readonly left: Item; readonly right: Item }
  | { readonly kind: "or"; readonly left: Item; readonly right: Item }
  | { readonly kind: "implies"; readonly antecedent: Item; readonly consequent: Item }
  | {
      readonly kind: "forall";
      readonly variable: string;
      readonly domain: string;
      readonly body: Item;
      readonly domainConstraint?: Item;
    }
  | {
      readonly kind: "exists";
      readonly variable: string;
      readonly domain: string;
      readonly body: Item;
      readonly domainConstraint?: Item;
    }
  | {
      readonly kind: "refl";
      readonly reflectedLevel: number;
      readonly targetBoundary: string;
      readonly targetPolarity: Polarity;
      readonly targetItem: Item;
    }
  | { readonly kind: "ref"; readonly name: string };

export type RecursiveDef = {
  readonly name: string;
  readonly level: number;
  readonly body: Item;
};

export type PositivityViolation =
  | "left-of-implies"
  | "polarity-flip"
  | "boundary-promotion"
  | "stratification-violation";

export type WellFormedResult =
  | { readonly ok: true; readonly minLevel: number }
  | { readonly ok: false; readonly violation: PositivityViolation; readonly reason: string };

/** Role-indexed relational claim R(r1: t1, ..., rn: tn). */
export function atom(relation: string, roles: readonly RoleArg[] = []): Item {
  return { kind: "atom", relation, roles };
}

/** Unsatisfiable item bottom (never witnessed on non-empty boundaries). */
export function bottom(): Item {
  return { kind: "bottom" };
}

/** Boundary-scoped congruence t1 ≈_B t2. */
export function equiv(boundary: string, left: string, right: string): Item {
  return { kind: "equiv", boundary, left, right };
}

/** Strong polarity flip ~A (Sanskrit paryudasa). */
export function flip(inner: Item): Item {
  return { kind: "flip", inner };
}

/** Dual-polarity conjunction A ∧ C. */
export function and(left: Item, right: Item): Item {
  return { kind: "and", left, right };
}

/** Cover-witnessed disjunction A ∨ C. */
export function or(left: Item, right: Item): Item {
  return { kind: "or", left, right };
}

/** Scoped conditional A → C. */
export function implies(antecedent: Item, consequent: Item): Item {
  return { kind: "implies", antecedent, consequent };
}

/** Structural impossibility shorthand: ¬_⊥ A := A → ⊥. */
export function structImposs(inner: Item): Item {
  return implies(inner, bottom());
}

/** Boundary-scoped universal quantifier ∀(x : D) A(x), with optional constraint [δ]. */
export function forall(
  variable: string,
  domain: string,
  body: Item,
  domainConstraint?: Item,
): Item {
  return domainConstraint !== undefined
    ? { kind: "forall", variable, domain, body, domainConstraint }
    : { kind: "forall", variable, domain, body };
}

/** Boundary-scoped existential quantifier ∃(x : D) A(x), with optional constraint [δ]. */
export function exists(
  variable: string,
  domain: string,
  body: Item,
  domainConstraint?: Item,
): Item {
  return domainConstraint !== undefined
    ? { kind: "exists", variable, domain, body, domainConstraint }
    : { kind: "exists", variable, domain, body };
}

/** Stratified reflection Refl_k(B ⊩± A) on a judgment of level k < n. */
export function refl(
  reflectedLevel: number,
  targetBoundary: string,
  targetPolarity: Polarity,
  targetItem: Item,
): Item {
  return { kind: "refl", reflectedLevel, targetBoundary, targetPolarity, targetItem };
}

/** Named reference inside recursive definitions. */
export function ref(name: string): Item {
  return { kind: "ref", name };
}

/** Canonical deterministic string key for structural equality and indexing. */
export function itemKey(item: Item): string {
  switch (item.kind) {
    case "atom": {
      const sortedRoles = [...item.roles].sort((a, b) =>
        a.role === b.role ? a.handle.localeCompare(b.handle) : a.role.localeCompare(b.role),
      );
      const rendered = sortedRoles.map((r) => `${r.role}:${r.handle}`).join(",");
      return `${item.relation}(${rendered})`;
    }
    case "bottom":
      return "⊥";
    case "equiv":
      return `(${item.left} ≈_${item.boundary} ${item.right})`;
    case "flip":
      return `~(${itemKey(item.inner)})`;
    case "and":
      return `(${itemKey(item.left)} ∧ ${itemKey(item.right)})`;
    case "or":
      return `(${itemKey(item.left)} ∨ ${itemKey(item.right)})`;
    case "implies":
      return `(${itemKey(item.antecedent)} → ${itemKey(item.consequent)})`;
    case "forall": {
      const dom = item.domainConstraint !== undefined
        ? `${item.domain} ⊓ [${itemKey(item.domainConstraint)}]`
        : item.domain;
      return `∀(${item.variable}:${dom}).${itemKey(item.body)}`;
    }
    case "exists": {
      const dom = item.domainConstraint !== undefined
        ? `${item.domain} ⊓ [${itemKey(item.domainConstraint)}]`
        : item.domain;
      return `∃(${item.variable}:${dom}).${itemKey(item.body)}`;
    }
    case "refl":
      return `Refl_${item.reflectedLevel}(${item.targetBoundary} ⊩${item.targetPolarity} ${itemKey(item.targetItem)})`;
    case "ref":
      return `@${item.name}`;
  }
}

/** Capture-avoiding handle substitution for single-variable instantiations. */
export function substituteHandle(item: Item, variable: string, replacement: string): Item {
  switch (item.kind) {
    case "atom":
      return atom(
        item.relation,
        item.roles.map((r) =>
          r.handle === variable ? { role: r.role, handle: replacement } : r,
        ),
      );
    case "bottom":
    case "ref":
      return item;
    case "equiv":
      return equiv(
        item.boundary,
        item.left === variable ? replacement : item.left,
        item.right === variable ? replacement : item.right,
      );
    case "flip":
      return flip(substituteHandle(item.inner, variable, replacement));
    case "and":
      return and(
        substituteHandle(item.left, variable, replacement),
        substituteHandle(item.right, variable, replacement),
      );
    case "or":
      return or(
        substituteHandle(item.left, variable, replacement),
        substituteHandle(item.right, variable, replacement),
      );
    case "implies":
      return implies(
        substituteHandle(item.antecedent, variable, replacement),
        substituteHandle(item.consequent, variable, replacement),
      );
    case "forall":
      if (item.variable === variable) {
        return item;
      }
      return forall(
        item.variable,
        item.domain,
        substituteHandle(item.body, variable, replacement),
        item.domainConstraint !== undefined
          ? substituteHandle(item.domainConstraint, variable, replacement)
          : undefined,
      );
    case "exists":
      if (item.variable === variable) {
        return item;
      }
      return exists(
        item.variable,
        item.domain,
        substituteHandle(item.body, variable, replacement),
        item.domainConstraint !== undefined
          ? substituteHandle(item.domainConstraint, variable, replacement)
          : undefined,
      );
    case "refl":
      return refl(
        item.reflectedLevel,
        item.targetBoundary,
        item.targetPolarity,
        substituteHandle(item.targetItem, variable, replacement),
      );
  }
}

/** Collect all relation symbol names occurring anywhere inside an item. */
export function collectRelations(item: Item): Set<string> {
  const out = new Set<string>();
  walkItem(item, (node) => {
    if (node.kind === "atom") {
      out.add(node.relation);
    } else if (node.kind === "equiv") {
      out.add(`≈_${node.boundary}`);
    }
  });
  return out;
}

/** Collect all free constant/handle identifiers occurring inside an item. */
export function collectHandles(item: Item): Set<string> {
  const out = new Set<string>();
  function visit(node: Item, bound: ReadonlySet<string>): void {
    switch (node.kind) {
      case "atom":
        for (const r of node.roles) {
          if (!bound.has(r.handle)) {
            out.add(r.handle);
          }
        }
        return;
      case "equiv":
        if (!bound.has(node.left)) {
          out.add(node.left);
        }
        if (!bound.has(node.right)) {
          out.add(node.right);
        }
        return;
      case "bottom":
      case "ref":
        return;
      case "flip":
        visit(node.inner, bound);
        return;
      case "and":
      case "or":
        visit(node.left, bound);
        visit(node.right, bound);
        return;
      case "implies":
        visit(node.antecedent, bound);
        visit(node.consequent, bound);
        return;
      case "forall":
      case "exists": {
        const nextBound = new Set(bound);
        nextBound.add(node.variable);
        if (node.domainConstraint !== undefined) {
          visit(node.domainConstraint, nextBound);
        }
        visit(node.body, nextBound);
        return;
      }
      case "refl":
        visit(node.targetItem, bound);
        return;
    }
  }
  visit(item, new Set());
  return out;
}

/** Compute the minimum stratification level required by an item. */
export function computeItemLevel(
  item: Item,
  knownLevels: ReadonlyMap<string, number> = new Map(),
): number {
  switch (item.kind) {
    case "atom":
    case "bottom":
    case "equiv":
      return 0;
    case "ref":
      return knownLevels.get(item.name) ?? 0;
    case "flip":
      return computeItemLevel(item.inner, knownLevels);
    case "and":
    case "or":
      return Math.max(
        computeItemLevel(item.left, knownLevels),
        computeItemLevel(item.right, knownLevels),
      );
    case "implies":
      return Math.max(
        computeItemLevel(item.antecedent, knownLevels),
        computeItemLevel(item.consequent, knownLevels),
      );
    case "forall":
    case "exists": {
      const bodyLevel = computeItemLevel(item.body, knownLevels);
      const constraintLevel =
        item.domainConstraint !== undefined
          ? computeItemLevel(item.domainConstraint, knownLevels)
          : 0;
      return Math.max(bodyLevel, constraintLevel);
    }
    case "refl": {
      const innerLevel = computeItemLevel(item.targetItem, knownLevels);
      return Math.max(item.reflectedLevel + 1, innerLevel + 1);
    }
  }
}

/**
 * Validate a recursive definition against the Curry Paradox firewall:
 * 1) Level Stratification: every Refl_k(J) requires level(J) <= k and k < def.level.
 * 2) Strict Positivity: self-reference never occurs left of `→`, inside `~`,
 *    or inside a contravariant boundary promotion `[X]` / quantifier domain.
 */
export function checkRecursiveDefinition(
  def: RecursiveDef,
  knownLevels: ReadonlyMap<string, number> = new Map(),
): WellFormedResult {
  if (!Number.isInteger(def.level) || def.level < 0) {
    return {
      ok: false,
      violation: "stratification-violation",
      reason: `Definition "${def.name}" has invalid level ${def.level}; level must be a non-negative integer.`,
    };
  }

  const levelsWithSelf = new Map(knownLevels);
  levelsWithSelf.set(def.name, def.level);

  function checkNode(
    node: Item,
    inAntecedent: boolean,
    inFlip: boolean,
    inDomainConstraint: boolean,
  ): PositivityViolation | undefined {
    switch (node.kind) {
      case "atom":
      case "bottom":
      case "equiv":
        return undefined;
      case "ref":
        if (node.name !== def.name) {
          return undefined;
        }
        if (inDomainConstraint) {
          return "boundary-promotion";
        }
        if (inFlip) {
          return "polarity-flip";
        }
        if (inAntecedent) {
          return "left-of-implies";
        }
        return undefined;
      case "flip":
        return checkNode(node.inner, inAntecedent, true, inDomainConstraint);
      case "and":
      case "or":
        return (
          checkNode(node.left, inAntecedent, inFlip, inDomainConstraint) ??
          checkNode(node.right, inAntecedent, inFlip, inDomainConstraint)
        );
      case "implies":
        return (
          checkNode(node.antecedent, true, inFlip, inDomainConstraint) ??
          checkNode(node.consequent, inAntecedent, inFlip, inDomainConstraint)
        );
      case "forall":
      case "exists": {
        if (node.domainConstraint !== undefined) {
          const domErr = checkNode(node.domainConstraint, inAntecedent, inFlip, true);
          if (domErr !== undefined) {
            return domErr;
          }
        }
        return checkNode(node.body, inAntecedent, inFlip, inDomainConstraint);
      }
      case "refl": {
        const targetLevel = computeItemLevel(node.targetItem, levelsWithSelf);
        if (targetLevel > node.reflectedLevel || node.reflectedLevel >= def.level) {
          return "stratification-violation";
        }
        return checkNode(node.targetItem, inAntecedent, inFlip, inDomainConstraint);
      }
    }
  }

  const violation = checkNode(def.body, false, false, false);
  if (violation !== undefined) {
    return {
      ok: false,
      violation,
      reason: `Recursive definition "${def.name}" at level ${def.level} failed ${violation}.`,
    };
  }

  const minLevel = computeItemLevel(def.body, knownLevels);
  if (def.level < minLevel) {
    return {
      ok: false,
      violation: "stratification-violation",
      reason: `Definition "${def.name}" declared level ${def.level} is below required body level ${minLevel}.`,
    };
  }

  return { ok: true, minLevel };
}

function walkItem(item: Item, visitor: (node: Item) => void): void {
  visitor(item);
  switch (item.kind) {
    case "atom":
    case "bottom":
    case "equiv":
    case "ref":
      return;
    case "flip":
      walkItem(item.inner, visitor);
      return;
    case "and":
    case "or":
      walkItem(item.left, visitor);
      walkItem(item.right, visitor);
      return;
    case "implies":
      walkItem(item.antecedent, visitor);
      walkItem(item.consequent, visitor);
      return;
    case "forall":
    case "exists":
      if (item.domainConstraint !== undefined) {
        walkItem(item.domainConstraint, visitor);
      }
      walkItem(item.body, visitor);
      return;
    case "refl":
      walkItem(item.targetItem, visitor);
      return;
  }
}
