/**
 * Prawitz-style natural deduction proof verifier for UL-Core, UL-Minimal, and
 * UL-Intuitionistic: hypothetical sub-proof discharge (→I), open-domain schematic
 * ∀I with strict eigenvariable freshness, ∃E, standalone Cover-Gluing, boundary-scoped
 * congruence, stratified cross-stage reflection (Refl_k@Σ_t), and mode-isolated ⊥E.
 *
 * Bridges verified derivations back into InquiryEngine with full base-leaf provenance.
 */

import { BOT_BOUNDARY, type BoundarySystem } from "./boundary.ts";
import { type EvaluationSnapshot, type GroundDependency, type InquiryEngine } from "./engine.ts";
import {
  and,
  collectAllIdentifiers,
  collectHandles,
  computeItemLevel,
  equiv,
  exists,
  flip,
  forall,
  implies,
  itemKey,
  or,
  substituteHandle,
  type Item,
  type Polarity,
} from "./syntax.ts";

export type DeductionMode = "UL-Core" | "UL-Minimal" | "UL-Intuitionistic";

export type ProofViolation =
  | "invalid-boundary"
  | "mode-precondition"
  | "ground-not-live"
  | "unknown-assumption"
  | "shadowed-assumption"
  | "type-mismatch"
  | "disjoint-meet"
  | "unknown-meet"
  | "unwitnessed-cover"
  | "eigenvariable-not-fresh"
  | "eigenvariable-escape"
  | "inadmissible-term"
  | "non-native-relation"
  | "stratification-violation"
  | "ex-falso-disallowed"
  | "open-assumptions";

export type ProofNode =
  | {
      readonly kind: "live-ground";
      readonly boundary: string;
      readonly polarity: Polarity;
      readonly item: Item;
    }
  | { readonly kind: "assume"; readonly assumptionId: string; readonly boundary: string }
  | { readonly kind: "weaken-boundary"; readonly proof: ProofNode; readonly toBoundary: string }
  | {
      readonly kind: "implies-intro";
      readonly boundary: string;
      readonly assumptionId: string;
      readonly antecedent: Item;
      readonly body: ProofNode;
    }
  | { readonly kind: "implies-elim"; readonly premise: ProofNode; readonly conditional: ProofNode }
  | { readonly kind: "and-intro"; readonly left: ProofNode; readonly right: ProofNode }
  | { readonly kind: "and-elim"; readonly pair: ProofNode; readonly side: "left" | "right" }
  | {
      readonly kind: "or-intro";
      readonly witness: ProofNode;
      readonly side: "left" | "right";
      readonly other: Item;
    }
  | {
      readonly kind: "or-cover-intro";
      readonly boundary: string;
      readonly left: Item;
      readonly right: Item;
      readonly cellProofs: readonly { readonly cell: string; readonly proof: ProofNode }[];
    }
  | {
      readonly kind: "or-elim";
      readonly disjunction: ProofNode;
      readonly leftAssumpId: string;
      readonly leftBranch: ProofNode;
      readonly rightAssumpId: string;
      readonly rightBranch: ProofNode;
    }
  | {
      readonly kind: "cover-glue";
      readonly boundary: string;
      readonly item: Item;
      readonly cellProofs: readonly { readonly cell: string; readonly proof: ProofNode }[];
    }
  | {
      readonly kind: "forall-intro";
      readonly boundary: string;
      readonly variable: string;
      readonly domain: string;
      readonly eigenvar: string;
      readonly templateBody: Item;
      readonly body: ProofNode;
      readonly domainConstraint?: Item;
      readonly constraintAssumpId?: string;
    }
  | {
      readonly kind: "forall-elim";
      readonly universal: ProofNode;
      readonly term: string;
      readonly constraintProof?: ProofNode;
    }
  | {
      readonly kind: "exists-intro";
      readonly witnessTerm: string;
      readonly variable: string;
      readonly domain: string;
      readonly templateBody: Item;
      readonly witnessProof: ProofNode;
      readonly domainConstraint?: Item;
      readonly constraintProof?: ProofNode;
    }
  | {
      readonly kind: "exists-elim";
      readonly existential: ProofNode;
      readonly witnessVar: string;
      readonly assumptionId: string;
      readonly body: ProofNode;
      readonly constraintAssumpId?: string;
    }
  | { readonly kind: "flip-intro"; readonly inner: ProofNode }
  | { readonly kind: "flip-elim"; readonly inner: ProofNode }
  | { readonly kind: "equiv-refl"; readonly boundary: string; readonly term: string }
  | {
      readonly kind: "equiv-subst";
      readonly equivProof: ProofNode;
      readonly targetProof: ProofNode;
      readonly direction: "left-to-right" | "right-to-left";
    }
  | { readonly kind: "refl-intro"; readonly boundary: string; readonly reflItem: Item }
  | { readonly kind: "ex-falso-bottom"; readonly bottomProof: ProofNode; readonly target: Item };

export type DerivationResult =
  | {
      readonly ok: true;
      readonly boundary: string;
      readonly polarity: Polarity;
      readonly item: Item;
      readonly requiredBaseIds: readonly string[];
      readonly requiredGrounds: readonly GroundDependency[];
    }
  | { readonly ok: false; readonly violation: ProofViolation; readonly reason: string };

type ActiveAssumption = {
  readonly boundary: string;
  readonly item: Item;
};

function mergeSorted(...lists: readonly (readonly string[])[]): readonly string[] {
  const out = new Set<string>();
  for (const list of lists) {
    for (const s of list) {
      out.add(s);
    }
  }
  return [...out].sort();
}

function mergeGroundDeps(
  ...lists: readonly (readonly GroundDependency[])[]
): readonly GroundDependency[] {
  const seen = new Set<string>();
  const out: GroundDependency[] = [];
  for (const list of lists) {
    for (const dep of list) {
      const k = `${dep.boundary}\0${dep.polarity}\0${itemKey(dep.item)}`;
      if (!seen.has(k)) {
        seen.add(k);
        out.push(dep);
      }
    }
  }
  return out;
}

function isDefinedNonEmptyBoundary(boundaries: BoundarySystem, boundary: string): boolean {
  if (boundary === BOT_BOUNDARY) {
    return false;
  }
  try {
    return boundaries.refines(boundary, boundary);
  } catch {
    return false;
  }
}

function isAdmissibleTerm(
  boundaries: BoundarySystem,
  term: string,
  domain: string,
  eigenScope: ReadonlyMap<string, string>,
): boolean {
  const eigenDom = eigenScope.get(term);
  if (eigenDom !== undefined) {
    return boundaries.refines(eigenDom, domain);
  }
  return boundaries.isAdmissibleHandle(domain, term);
}

function isHandleInAssumptions(
  handle: string,
  assumptions: ReadonlyMap<string, ActiveAssumption>,
): boolean {
  for (const assump of assumptions.values()) {
    if (collectHandles(assump.item).has(handle)) {
      return true;
    }
  }
  return false;
}

function verifyRoot(
  engine: InquiryEngine,
  snapshot: EvaluationSnapshot,
  stateHandles: ReadonlySet<string>,
  mode: DeductionMode,
  rootNode: ProofNode,
): DerivationResult {
  const boundaries = engine.boundaries;

  function verifyNode(
    node: ProofNode,
    assumptions: ReadonlyMap<string, ActiveAssumption>,
    eigenScope: ReadonlyMap<string, string>,
  ): DerivationResult {
    switch (node.kind) {
      case "live-ground": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Boundary "${node.boundary}" must be a defined non-empty boundary.`,
          };
        }
        const live = snapshot.liveGrounds(node.boundary, node.polarity, node.item);
        const entry = live[0];
        if (entry === undefined) {
          return {
            ok: false,
            violation: "ground-not-live",
            reason: `Ground (${node.boundary} ⊩${node.polarity} ${itemKey(node.item)}) is absent or quarantined.`,
          };
        }
        let requiredBaseIds: readonly string[] = [];
        if (entry.provenance.kind === "base") {
          requiredBaseIds = [entry.provenance.baseId];
        } else if (entry.provenance.kind === "derived") {
          requiredBaseIds = entry.provenance.baseLeaves.filter((l) => !l.startsWith("@"));
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: node.polarity,
          item: node.item,
          requiredBaseIds,
          requiredGrounds: [{ boundary: node.boundary, polarity: node.polarity, item: node.item }],
        };
      }

      case "assume": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Assumption boundary "${node.boundary}" must be defined and non-empty.`,
          };
        }
        const assumed = assumptions.get(node.assumptionId);
        if (assumed === undefined) {
          return {
            ok: false,
            violation: "unknown-assumption",
            reason: `Unknown assumption "${node.assumptionId}".`,
          };
        }
        if (!boundaries.refines(node.boundary, assumed.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Boundary "${node.boundary}" does not refine assumption scope "${assumed.boundary}".`,
          };
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: "+",
          item: assumed.item,
          requiredBaseIds: [],
          requiredGrounds: [],
        };
      }

      case "weaken-boundary": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.toBoundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Target boundary "${node.toBoundary}" must be defined and non-empty.`,
          };
        }
        const inner = verifyNode(node.proof, assumptions, eigenScope);
        if (!inner.ok) {
          return inner;
        }
        if (!boundaries.refines(node.toBoundary, inner.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Cannot weaken: "${node.toBoundary}" does not refine "${inner.boundary}".`,
          };
        }
        return {
          ok: true,
          boundary: node.toBoundary,
          polarity: inner.polarity,
          item: inner.item,
          requiredBaseIds: inner.requiredBaseIds,
          requiredGrounds: inner.requiredGrounds,
        };
      }

      case "implies-intro": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Conditional boundary "${node.boundary}" must be defined and non-empty.`,
          };
        }
        if (assumptions.has(node.assumptionId)) {
          return {
            ok: false,
            violation: "shadowed-assumption",
            reason: `Assumption identifier "${node.assumptionId}" shadows an active outer assumption.`,
          };
        }
        const nextAssumptions = new Map(assumptions);
        nextAssumptions.set(node.assumptionId, {
          boundary: node.boundary,
          item: node.antecedent,
        });
        const bodyRes = verifyNode(node.body, nextAssumptions, eigenScope);
        if (!bodyRes.ok) {
          return bodyRes;
        }
        if (bodyRes.polarity !== "+" || bodyRes.boundary !== node.boundary) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: `implies-intro body must derive (${node.boundary} ⊩+ consequent); got (${bodyRes.boundary} ⊩${bodyRes.polarity}).`,
          };
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: "+",
          item: implies(node.antecedent, bodyRes.item),
          requiredBaseIds: bodyRes.requiredBaseIds,
          requiredGrounds: bodyRes.requiredGrounds,
        };
      }

      case "implies-elim": {
        const pRes = verifyNode(node.premise, assumptions, eigenScope);
        if (!pRes.ok) {
          return pRes;
        }
        const cRes = verifyNode(node.conditional, assumptions, eigenScope);
        if (!cRes.ok) {
          return cRes;
        }
        if (pRes.polarity !== "+" || cRes.polarity !== "+" || cRes.item.kind !== "implies") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "implies-elim requires positive premise and positive conditional (A → C).",
          };
        }
        if (itemKey(pRes.item) !== itemKey(cRes.item.antecedent)) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: `implies-elim premise "${itemKey(pRes.item)}" does not match antecedent "${itemKey(cRes.item.antecedent)}".`,
          };
        }
        const meetStatus = boundaries.meetStatus(pRes.boundary, cRes.boundary);
        if (meetStatus.kind === "unknown") {
          return {
            ok: false,
            violation: "unknown-meet",
            reason: `The overlap of "${pRes.boundary}" and "${cRes.boundary}" is unknown; declare their meet or their disjointness.`,
          };
        }
        const meetB = meetStatus.kind === "overlap" ? meetStatus.meet : BOT_BOUNDARY;
        if (meetB === BOT_BOUNDARY) {
          return {
            ok: false,
            violation: "disjoint-meet",
            reason: `Disjoint boundaries "${pRes.boundary}" and "${cRes.boundary}" cannot apply Scoped Cut.`,
          };
        }
        return {
          ok: true,
          boundary: meetB,
          polarity: "+",
          item: cRes.item.consequent,
          requiredBaseIds: mergeSorted(pRes.requiredBaseIds, cRes.requiredBaseIds),
          requiredGrounds: mergeGroundDeps(pRes.requiredGrounds, cRes.requiredGrounds),
        };
      }

      case "and-intro": {
        const lRes = verifyNode(node.left, assumptions, eigenScope);
        if (!lRes.ok) {
          return lRes;
        }
        const rRes = verifyNode(node.right, assumptions, eigenScope);
        if (!rRes.ok) {
          return rRes;
        }
        if (lRes.polarity !== "+" || rRes.polarity !== "+") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "and-intro requires positive witnesses on both conjuncts.",
          };
        }
        const meetStatus = boundaries.meetStatus(lRes.boundary, rRes.boundary);
        if (meetStatus.kind === "unknown") {
          return {
            ok: false,
            violation: "unknown-meet",
            reason: `The overlap of "${lRes.boundary}" and "${rRes.boundary}" is unknown; declare their meet or their disjointness.`,
          };
        }
        const meetB = meetStatus.kind === "overlap" ? meetStatus.meet : BOT_BOUNDARY;
        if (meetB === BOT_BOUNDARY) {
          return {
            ok: false,
            violation: "disjoint-meet",
            reason: `Disjoint conjunct boundaries "${lRes.boundary}" and "${rRes.boundary}" have empty meet.`,
          };
        }
        return {
          ok: true,
          boundary: meetB,
          polarity: "+",
          item: and(lRes.item, rRes.item),
          requiredBaseIds: mergeSorted(lRes.requiredBaseIds, rRes.requiredBaseIds),
          requiredGrounds: mergeGroundDeps(lRes.requiredGrounds, rRes.requiredGrounds),
        };
      }

      case "and-elim": {
        const pRes = verifyNode(node.pair, assumptions, eigenScope);
        if (!pRes.ok) {
          return pRes;
        }
        if (pRes.polarity !== "+" || pRes.item.kind !== "and") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "and-elim requires a positive conjunction item (A ∧ C).",
          };
        }
        return {
          ok: true,
          boundary: pRes.boundary,
          polarity: "+",
          item: node.side === "left" ? pRes.item.left : pRes.item.right,
          requiredBaseIds: pRes.requiredBaseIds,
          requiredGrounds: pRes.requiredGrounds,
        };
      }

      case "or-intro": {
        const wRes = verifyNode(node.witness, assumptions, eigenScope);
        if (!wRes.ok) {
          return wRes;
        }
        if (wRes.polarity !== "+") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "or-intro requires a positive witness.",
          };
        }
        return {
          ok: true,
          boundary: wRes.boundary,
          polarity: "+",
          item: node.side === "left" ? or(wRes.item, node.other) : or(node.other, wRes.item),
          requiredBaseIds: wRes.requiredBaseIds,
          requiredGrounds: wRes.requiredGrounds,
        };
      }

      case "or-cover-intro": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Cover boundary "${node.boundary}" must be defined and non-empty.`,
          };
        }
        const cells = node.cellProofs.map((cp) => cp.cell);
        if (cells.length === 0 || !boundaries.isWitnessedCover(node.boundary, cells)) {
          return {
            ok: false,
            violation: "unwitnessed-cover",
            reason: `Cells [${cells.join(", ")}] do not form a witnessed exhaustive cover of "${node.boundary}".`,
          };
        }
        const leftK = itemKey(node.left);
        const rightK = itemKey(node.right);
        const reqs: (readonly string[])[] = [];
        const groundReqs: (readonly GroundDependency[])[] = [];
        for (const cp of node.cellProofs) {
          const cRes = verifyNode(cp.proof, assumptions, eigenScope);
          if (!cRes.ok) {
            return cRes;
          }
          const ck = itemKey(cRes.item);
          if (cRes.polarity !== "+" || cRes.boundary !== cp.cell || (ck !== leftK && ck !== rightK)) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: `Cover cell "${cp.cell}" must witness +(${leftK}) or +(${rightK}) on "${cp.cell}".`,
            };
          }
          reqs.push(cRes.requiredBaseIds);
          groundReqs.push(cRes.requiredGrounds);
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: "+",
          item: or(node.left, node.right),
          requiredBaseIds: mergeSorted(...reqs),
          requiredGrounds: mergeGroundDeps(...groundReqs),
        };
      }

      case "or-elim": {
        const dRes = verifyNode(node.disjunction, assumptions, eigenScope);
        if (!dRes.ok) {
          return dRes;
        }
        if (dRes.polarity !== "+" || dRes.item.kind !== "or") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "or-elim requires a positive disjunction (A ∨ C).",
          };
        }
        if (assumptions.has(node.leftAssumpId) || assumptions.has(node.rightAssumpId)) {
          return {
            ok: false,
            violation: "shadowed-assumption",
            reason: "or-elim branch assumption identifier shadows an active outer assumption.",
          };
        }
        const leftAssumptions = new Map(assumptions);
        leftAssumptions.set(node.leftAssumpId, {
          boundary: dRes.boundary,
          item: dRes.item.left,
        });
        const lRes = verifyNode(node.leftBranch, leftAssumptions, eigenScope);
        if (!lRes.ok) {
          return lRes;
        }

        const rightAssumptions = new Map(assumptions);
        rightAssumptions.set(node.rightAssumpId, {
          boundary: dRes.boundary,
          item: dRes.item.right,
        });
        const rRes = verifyNode(node.rightBranch, rightAssumptions, eigenScope);
        if (!rRes.ok) {
          return rRes;
        }

        if (
          lRes.polarity !== "+" ||
          rRes.polarity !== "+" ||
          lRes.boundary !== dRes.boundary ||
          rRes.boundary !== dRes.boundary ||
          itemKey(lRes.item) !== itemKey(rRes.item)
        ) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: `or-elim branches must positively derive the same item on "${dRes.boundary}".`,
          };
        }
        return {
          ok: true,
          boundary: dRes.boundary,
          polarity: "+",
          item: lRes.item,
          requiredBaseIds: mergeSorted(
            dRes.requiredBaseIds,
            lRes.requiredBaseIds,
            rRes.requiredBaseIds,
          ),
          requiredGrounds: mergeGroundDeps(
            dRes.requiredGrounds,
            lRes.requiredGrounds,
            rRes.requiredGrounds,
          ),
        };
      }

      case "cover-glue": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Cover-glue boundary "${node.boundary}" must be defined and non-empty.`,
          };
        }
        const cells = node.cellProofs.map((cp) => cp.cell);
        if (cells.length === 0 || !boundaries.isWitnessedCover(node.boundary, cells)) {
          return {
            ok: false,
            violation: "unwitnessed-cover",
            reason: `Cells [${cells.join(", ")}] do not form a witnessed exhaustive cover of "${node.boundary}".`,
          };
        }
        const targetK = itemKey(node.item);
        let agreedPol: Polarity | undefined;
        const reqs: (readonly string[])[] = [];
        const groundReqs: (readonly GroundDependency[])[] = [];
        for (const cp of node.cellProofs) {
          const cRes = verifyNode(cp.proof, assumptions, eigenScope);
          if (!cRes.ok) {
            return cRes;
          }
          if (cRes.boundary !== cp.cell || itemKey(cRes.item) !== targetK) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: `cover-glue cell "${cp.cell}" must match item "${targetK}" on "${cp.cell}".`,
            };
          }
          if (agreedPol === undefined) {
            agreedPol = cRes.polarity;
          } else if (cRes.polarity !== agreedPol) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: `cover-glue cells disagree on polarity for "${targetK}".`,
            };
          }
          reqs.push(cRes.requiredBaseIds);
          groundReqs.push(cRes.requiredGrounds);
        }
        if (agreedPol === undefined) {
          return {
            ok: false,
            violation: "unwitnessed-cover",
            reason: "cover-glue requires at least one non-empty cell proof.",
          };
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: agreedPol,
          item: node.item,
          requiredBaseIds: mergeSorted(...reqs),
          requiredGrounds: mergeGroundDeps(...groundReqs),
        };
      }

      case "forall-intro": {
        if (
          !isDefinedNonEmptyBoundary(boundaries, node.boundary) ||
          !isDefinedNonEmptyBoundary(boundaries, node.domain)
        ) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `forall-intro requires defined non-empty boundary "${node.boundary}" and domain "${node.domain}".`,
          };
        }
        const hasCons = node.domainConstraint !== undefined;
        const hasAssump = node.constraintAssumpId !== undefined;
        if (hasCons !== hasAssump) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "forall-intro must pair domainConstraint with constraintAssumpId.",
          };
        }
        if (node.constraintAssumpId !== undefined && assumptions.has(node.constraintAssumpId)) {
          return {
            ok: false,
            violation: "shadowed-assumption",
            reason: `Constraint assumption identifier "${node.constraintAssumpId}" shadows an active outer assumption.`,
          };
        }
        const qItem = forall(node.variable, node.domain, node.templateBody, node.domainConstraint);
        if (
          eigenScope.has(node.eigenvar) ||
          stateHandles.has(node.eigenvar) ||
          isHandleInAssumptions(node.eigenvar, assumptions) ||
          collectAllIdentifiers(qItem).has(node.eigenvar)
        ) {
          return {
            ok: false,
            violation: "eigenvariable-not-fresh",
            reason: `Eigenvariable "${node.eigenvar}" is not fresh with respect to Σ, assumptions, or template.`,
          };
        }
        const nextEigen = new Map(eigenScope);
        nextEigen.set(node.eigenvar, node.domain);
        const nextAssumptions = new Map(assumptions);
        if (node.domainConstraint !== undefined && node.constraintAssumpId !== undefined) {
          nextAssumptions.set(node.constraintAssumpId, {
            boundary: node.boundary,
            item: substituteHandle(node.domainConstraint, node.variable, node.eigenvar),
          });
        }
        const bRes = verifyNode(node.body, nextAssumptions, nextEigen);
        if (!bRes.ok) {
          return bRes;
        }
        const expectedBody = substituteHandle(node.templateBody, node.variable, node.eigenvar);
        if (
          bRes.polarity !== "+" ||
          bRes.boundary !== node.boundary ||
          itemKey(bRes.item) !== itemKey(expectedBody)
        ) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: `forall-intro body must derive (${node.boundary} ⊩+ ${itemKey(expectedBody)}).`,
          };
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: "+",
          item: qItem,
          requiredBaseIds: bRes.requiredBaseIds,
          requiredGrounds: bRes.requiredGrounds,
        };
      }

      case "forall-elim": {
        const uRes = verifyNode(node.universal, assumptions, eigenScope);
        if (!uRes.ok) {
          return uRes;
        }
        if (uRes.polarity !== "+" || uRes.item.kind !== "forall") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "forall-elim requires a positive universal item ∀(x : D) A(x).",
          };
        }
        if (!isAdmissibleTerm(boundaries, node.term, uRes.item.domain, eigenScope)) {
          return {
            ok: false,
            violation: "inadmissible-term",
            reason: `Term "${node.term}" is neither a scoped eigenvariable nor an admissible handle in "${uRes.item.domain}".`,
          };
        }
        if (uRes.item.domainConstraint !== undefined) {
          if (node.constraintProof === undefined) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: `forall-elim on constrained universal "${itemKey(uRes.item)}" requires constraintProof.`,
            };
          }
          const expectedCons = substituteHandle(
            uRes.item.domainConstraint,
            uRes.item.variable,
            node.term,
          );
          const cRes = verifyNode(node.constraintProof, assumptions, eigenScope);
          if (!cRes.ok) {
            return cRes;
          }
          if (
            cRes.polarity !== "+" ||
            cRes.boundary !== uRes.boundary ||
            itemKey(cRes.item) !== itemKey(expectedCons)
          ) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: `forall-elim constraintProof must derive (${uRes.boundary} ⊩+ ${itemKey(expectedCons)}).`,
            };
          }
          return {
            ok: true,
            boundary: uRes.boundary,
            polarity: "+",
            item: substituteHandle(uRes.item.body, uRes.item.variable, node.term),
            requiredBaseIds: mergeSorted(uRes.requiredBaseIds, cRes.requiredBaseIds),
            requiredGrounds: mergeGroundDeps(uRes.requiredGrounds, cRes.requiredGrounds),
          };
        }
        if (node.constraintProof !== undefined) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "forall-elim received constraintProof for an unconstrained universal.",
          };
        }
        return {
          ok: true,
          boundary: uRes.boundary,
          polarity: "+",
          item: substituteHandle(uRes.item.body, uRes.item.variable, node.term),
          requiredBaseIds: uRes.requiredBaseIds,
          requiredGrounds: uRes.requiredGrounds,
        };
      }

      case "exists-intro": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.domain)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Existential domain "${node.domain}" must be defined and non-empty.`,
          };
        }
        const hasCons = node.domainConstraint !== undefined;
        const hasProof = node.constraintProof !== undefined;
        if (hasCons !== hasProof) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "exists-intro must pair domainConstraint with constraintProof.",
          };
        }
        if (!isAdmissibleTerm(boundaries, node.witnessTerm, node.domain, eigenScope)) {
          return {
            ok: false,
            violation: "inadmissible-term",
            reason: `Witness term "${node.witnessTerm}" is not admissible in domain "${node.domain}".`,
          };
        }
        const wRes = verifyNode(node.witnessProof, assumptions, eigenScope);
        if (!wRes.ok) {
          return wRes;
        }
        const expected = substituteHandle(node.templateBody, node.variable, node.witnessTerm);
        if (wRes.polarity !== "+" || itemKey(wRes.item) !== itemKey(expected)) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: `exists-intro witness proof must derive +(${itemKey(expected)}).`,
          };
        }
        if (node.domainConstraint !== undefined && node.constraintProof !== undefined) {
          const cRes = verifyNode(node.constraintProof, assumptions, eigenScope);
          if (!cRes.ok) {
            return cRes;
          }
          const expectedCons = substituteHandle(
            node.domainConstraint,
            node.variable,
            node.witnessTerm,
          );
          if (
            cRes.polarity !== "+" ||
            cRes.boundary !== wRes.boundary ||
            itemKey(cRes.item) !== itemKey(expectedCons)
          ) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: `exists-intro constraintProof must derive (${wRes.boundary} ⊩+ ${itemKey(expectedCons)}).`,
            };
          }
          return {
            ok: true,
            boundary: wRes.boundary,
            polarity: "+",
            item: exists(node.variable, node.domain, node.templateBody, node.domainConstraint),
            requiredBaseIds: mergeSorted(wRes.requiredBaseIds, cRes.requiredBaseIds),
            requiredGrounds: mergeGroundDeps(wRes.requiredGrounds, cRes.requiredGrounds),
          };
        }
        return {
          ok: true,
          boundary: wRes.boundary,
          polarity: "+",
          item: exists(node.variable, node.domain, node.templateBody),
          requiredBaseIds: wRes.requiredBaseIds,
          requiredGrounds: wRes.requiredGrounds,
        };
      }

      case "exists-elim": {
        const eRes = verifyNode(node.existential, assumptions, eigenScope);
        if (!eRes.ok) {
          return eRes;
        }
        if (eRes.polarity !== "+" || eRes.item.kind !== "exists") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "exists-elim requires a positive existential item ∃(x : D) A(x).",
          };
        }
        if (
          eigenScope.has(node.witnessVar) ||
          stateHandles.has(node.witnessVar) ||
          isHandleInAssumptions(node.witnessVar, assumptions) ||
          collectAllIdentifiers(eRes.item).has(node.witnessVar)
        ) {
          return {
            ok: false,
            violation: "eigenvariable-not-fresh",
            reason: `Existential witness variable "${node.witnessVar}" is not fresh.`,
          };
        }
        if (assumptions.has(node.assumptionId)) {
          return {
            ok: false,
            violation: "shadowed-assumption",
            reason: `Assumption identifier "${node.assumptionId}" shadows an active outer assumption.`,
          };
        }
        if (node.constraintAssumpId !== undefined) {
          if (eRes.item.domainConstraint === undefined) {
            return {
              ok: false,
              violation: "type-mismatch",
              reason: "exists-elim cannot bind constraintAssumpId when existential has no domainConstraint.",
            };
          }
          if (
            assumptions.has(node.constraintAssumpId) ||
            node.constraintAssumpId === node.assumptionId
          ) {
            return {
              ok: false,
              violation: "shadowed-assumption",
              reason: `Constraint assumption identifier "${node.constraintAssumpId}" shadows an active or peer assumption.`,
            };
          }
        }
        const nextEigen = new Map(eigenScope);
        nextEigen.set(node.witnessVar, eRes.item.domain);
        const nextAssumptions = new Map(assumptions);
        nextAssumptions.set(node.assumptionId, {
          boundary: eRes.boundary,
          item: substituteHandle(eRes.item.body, eRes.item.variable, node.witnessVar),
        });
        if (node.constraintAssumpId !== undefined && eRes.item.domainConstraint !== undefined) {
          nextAssumptions.set(node.constraintAssumpId, {
            boundary: eRes.boundary,
            item: substituteHandle(
              eRes.item.domainConstraint,
              eRes.item.variable,
              node.witnessVar,
            ),
          });
        }
        const bRes = verifyNode(node.body, nextAssumptions, nextEigen);
        if (!bRes.ok) {
          return bRes;
        }
        if (bRes.polarity !== "+" || bRes.boundary !== eRes.boundary) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: `exists-elim body must derive (${eRes.boundary} ⊩+ E).`,
          };
        }
        if (collectHandles(bRes.item).has(node.witnessVar)) {
          return {
            ok: false,
            violation: "eigenvariable-escape",
            reason: `Existential witness variable "${node.witnessVar}" escapes into conclusion "${itemKey(bRes.item)}".`,
          };
        }
        return {
          ok: true,
          boundary: eRes.boundary,
          polarity: "+",
          item: bRes.item,
          requiredBaseIds: mergeSorted(eRes.requiredBaseIds, bRes.requiredBaseIds),
          requiredGrounds: mergeGroundDeps(eRes.requiredGrounds, bRes.requiredGrounds),
        };
      }

      case "flip-intro": {
        const iRes = verifyNode(node.inner, assumptions, eigenScope);
        if (!iRes.ok) {
          return iRes;
        }
        return {
          ok: true,
          boundary: iRes.boundary,
          polarity: iRes.polarity === "+" ? "-" : "+",
          item: flip(iRes.item),
          requiredBaseIds: iRes.requiredBaseIds,
          requiredGrounds: iRes.requiredGrounds,
        };
      }

      case "flip-elim": {
        const iRes = verifyNode(node.inner, assumptions, eigenScope);
        if (!iRes.ok) {
          return iRes;
        }
        if (iRes.item.kind !== "flip") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "flip-elim requires an item of form ~A.",
          };
        }
        return {
          ok: true,
          boundary: iRes.boundary,
          polarity: iRes.polarity === "+" ? "-" : "+",
          item: iRes.item.inner,
          requiredBaseIds: iRes.requiredBaseIds,
          requiredGrounds: iRes.requiredGrounds,
        };
      }

      case "equiv-refl": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Reflexivity boundary "${node.boundary}" must be defined and non-empty.`,
          };
        }
        if (!isAdmissibleTerm(boundaries, node.term, node.boundary, eigenScope)) {
          return {
            ok: false,
            violation: "inadmissible-term",
            reason: `Term "${node.term}" is not admissible in "${node.boundary}".`,
          };
        }
        return {
          ok: true,
          boundary: node.boundary,
          polarity: "+",
          item: equiv(node.boundary, node.term, node.term),
          requiredBaseIds: [],
          requiredGrounds: [],
        };
      }

      case "equiv-subst": {
        const eqRes = verifyNode(node.equivProof, assumptions, eigenScope);
        if (!eqRes.ok) {
          return eqRes;
        }
        const tRes = verifyNode(node.targetProof, assumptions, eigenScope);
        if (!tRes.ok) {
          return tRes;
        }
        if (eqRes.polarity !== "+" || eqRes.item.kind !== "equiv" || tRes.item.kind !== "atom") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "equiv-subst requires positive (t1 ≈_B t2) and an atomic relational item.",
          };
        }
        const meetStatus = boundaries.meetStatus(eqRes.boundary, tRes.boundary);
        if (meetStatus.kind === "unknown") {
          return {
            ok: false,
            violation: "unknown-meet",
            reason: `The overlap of "${eqRes.boundary}" and "${tRes.boundary}" is unknown; declare their meet or their disjointness.`,
          };
        }
        const meetB = meetStatus.kind === "overlap" ? meetStatus.meet : BOT_BOUNDARY;
        if (meetB === BOT_BOUNDARY) {
          return {
            ok: false,
            violation: "disjoint-meet",
            reason: `Disjoint boundaries "${eqRes.boundary}" and "${tRes.boundary}" cannot substitute equivalence.`,
          };
        }
        if (
          !boundaries.refines(eqRes.boundary, eqRes.item.boundary) ||
          !boundaries.hasNativeRelation(eqRes.item.boundary, tRes.item.relation)
        ) {
          return {
            ok: false,
            violation: "non-native-relation",
            reason: `Relation "${tRes.item.relation}" is not native to congruence boundary "${eqRes.item.boundary}".`,
          };
        }
        const fromHandle = node.direction === "left-to-right" ? eqRes.item.left : eqRes.item.right;
        const toHandle = node.direction === "left-to-right" ? eqRes.item.right : eqRes.item.left;
        const rewritten: Item = {
          kind: "atom",
          relation: tRes.item.relation,
          roles: tRes.item.roles.map((r) =>
            r.handle === fromHandle ? { role: r.role, handle: toHandle } : r,
          ),
        };
        return {
          ok: true,
          boundary: meetB,
          polarity: tRes.polarity,
          item: rewritten,
          requiredBaseIds: mergeSorted(eqRes.requiredBaseIds, tRes.requiredBaseIds),
          requiredGrounds: mergeGroundDeps(eqRes.requiredGrounds, tRes.requiredGrounds),
        };
      }

      case "refl-intro": {
        if (!isDefinedNonEmptyBoundary(boundaries, node.boundary)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Reflection boundary "${node.boundary}" must be defined and non-empty.`,
          };
        }
        if (node.reflItem.kind !== "refl" || node.reflItem.targetStage === undefined) {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "refl-intro requires a stage-indexed reflection item Refl_k@Σ_t(J).",
          };
        }
        const {
          reflectedLevel,
          targetBoundary,
          targetPolarity,
          targetItem,
          targetStage,
          targetStatus,
        } = node.reflItem;
        if (!Number.isInteger(targetStage) || targetStage < 0 || targetStage >= engine.stage) {
          return {
            ok: false,
            violation: "stratification-violation",
            reason: `Cross-stage reflection target stage ${targetStage} must satisfy 0 <= t < current stage ${engine.stage}.`,
          };
        }
        const requiredLevel = computeItemLevel(targetItem);
        if (!Number.isInteger(reflectedLevel) || reflectedLevel < requiredLevel) {
          return {
            ok: false,
            violation: "stratification-violation",
            reason: `Reflection level ${reflectedLevel} cannot reflect item requiring level ${requiredLevel}.`,
          };
        }
        if (!engine.isReflectionWellScopedAtStage(targetStage, targetBoundary, targetItem)) {
          return {
            ok: false,
            violation: "invalid-boundary",
            reason: `Reflected target boundary "${targetBoundary}" or inner boundary reference was not defined and non-empty at stage Σ_${targetStage}.`,
          };
        }
        const priorSnap = engine.evaluateAtStage(targetStage, [targetItem]);
        const holds =
          targetStatus !== undefined
            ? priorSnap.localStatus(targetBoundary, targetItem) === targetStatus
            : priorSnap.isLive(targetBoundary, targetPolarity, targetItem);
        return {
          ok: true,
          boundary: node.boundary,
          polarity: holds ? "+" : "-",
          item: node.reflItem,
          requiredBaseIds: [],
          requiredGrounds: [],
        };
      }

      case "ex-falso-bottom": {
        if (mode !== "UL-Intuitionistic") {
          return {
            ok: false,
            violation: "ex-falso-disallowed",
            reason: `Rule ex-falso-bottom (⊥ → C) is disallowed in mode "${mode}" (requires "UL-Intuitionistic").`,
          };
        }
        const bRes = verifyNode(node.bottomProof, assumptions, eigenScope);
        if (!bRes.ok) {
          return bRes;
        }
        if (bRes.polarity !== "+" || bRes.item.kind !== "bottom") {
          return {
            ok: false,
            violation: "type-mismatch",
            reason: "ex-falso-bottom requires a positive derivation of ⊥.",
          };
        }
        return {
          ok: true,
          boundary: bRes.boundary,
          polarity: "+",
          item: node.target,
          requiredBaseIds: bRes.requiredBaseIds,
          requiredGrounds: bRes.requiredGrounds,
        };
      }
    }
  }

  return verifyNode(rootNode, new Map<string, ActiveAssumption>(), new Map<string, string>());
}

function collectLiveGroundItems(node: ProofNode): readonly Item[] {
  const out: Item[] = [];
  const visit = (n: ProofNode): void => {
    switch (n.kind) {
      case "live-ground":
        out.push(n.item);
        return;
      case "assume":
      case "equiv-refl":
      case "refl-intro":
        return;
      case "weaken-boundary":
        visit(n.proof);
        return;
      case "implies-intro":
      case "forall-intro":
      case "flip-intro":
      case "flip-elim":
        visit(n.kind === "implies-intro" || n.kind === "forall-intro" ? n.body : n.inner);
        return;
      case "implies-elim":
        visit(n.premise);
        visit(n.conditional);
        return;
      case "and-intro":
        visit(n.left);
        visit(n.right);
        return;
      case "and-elim":
        visit(n.pair);
        return;
      case "or-intro":
        visit(n.witness);
        return;
      case "or-cover-intro":
      case "cover-glue":
        for (const cp of n.cellProofs) {
          visit(cp.proof);
        }
        return;
      case "or-elim":
        visit(n.disjunction);
        visit(n.leftBranch);
        visit(n.rightBranch);
        return;
      case "forall-elim":
        visit(n.universal);
        if (n.constraintProof !== undefined) {
          visit(n.constraintProof);
        }
        return;
      case "exists-intro":
        visit(n.witnessProof);
        if (n.constraintProof !== undefined) {
          visit(n.constraintProof);
        }
        return;
      case "exists-elim":
        visit(n.existential);
        visit(n.body);
        return;
      case "equiv-subst":
        visit(n.equivProof);
        visit(n.targetProof);
        return;
      case "ex-falso-bottom":
        visit(n.bottomProof);
        return;
    }
  };
  visit(node);
  return out;
}

/**
 * Verify a natural-deduction proof tree against `engine`'s current evaluation state Σ
 * under the specified deductive tier (`UL-Core`, `UL-Minimal`, or `UL-Intuitionistic`).
 */
export function verifyDerivation(
  engine: InquiryEngine,
  proof: ProofNode,
  mode: DeductionMode = "UL-Core",
): DerivationResult {
  const snapshot = engine.evaluate(collectLiveGroundItems(proof));
  if (mode === "UL-Minimal" || mode === "UL-Intuitionistic") {
    if (!engine.monotoneOnly || !snapshot.isCollisionFree()) {
      return {
        ok: false,
        violation: "mode-precondition",
        reason: `Mode "${mode}" requires monotoneOnly Σ and No-Gluts (zero collisions).`,
      };
    }
  }
  const stateHandles = engine.mentionedHandles();
  return verifyRoot(engine, snapshot, stateHandles, mode, proof);
}

/**
 * Verify `proof` and, if valid, admit the derived judgment back into `engine` as a
 * named theorem anchored to its underlying base leaves (`requiredBaseIds`).
 */
export function admitVerifiedDerivation(
  engine: InquiryEngine,
  proof: ProofNode,
  theoremId: string,
  mode: DeductionMode = "UL-Core",
): DerivationResult {
  const res = verifyDerivation(engine, proof, mode);
  if (res.ok) {
    engine.recordTheorem(
      res.boundary,
      res.polarity,
      res.item,
      theoremId,
      res.requiredBaseIds,
      res.requiredGrounds,
    );
  }
  return res;
}
