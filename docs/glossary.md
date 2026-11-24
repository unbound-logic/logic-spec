---
title: Terminology Registry & Semantic Boundaries
status: active
date: 2026-11-25
---

# Terminology Registry

This registry enforces Guardrail 3 (**Terminology Hygiene**) from [AGENTS.md](../AGENTS.md). Every loaded term inherited from classical or modern formal logic is explicitly quarantined until its local semantic boundary is settled; every local primitive or derived term links to the governing decision in [docs/design-review.md](design-review.md).

## 1. Quarantined Classical Terms

Do **not** use these terms as unexamined primitives in specification prose or formal rules. When referencing them for historical comparison, mark the classical context explicitly.

| Term | Classical / Inherited Meaning | Local Operational Boundary | Status |
| :--- | :--- | :--- | :--- |
| **Truth** | Static, context-free bivalent property (`T`) often presupposing mind-independent correspondence or Platonic abstracta. | Suspended as a primitive. Replaced at the ground floor by scoped **Witness (`+`)** and **Exclusion (`-`)** under [`layer1-dual-polarity`](design-review.md#layer1-dual-polarity); classical truth-aptness is targeted only as a boundary specialization ([`scope-anchor-unified-core`](design-review.md#scope-anchor-unified-core)). | quarantined |
| **Proposition** | Context-free, timeless declarative sentence determinately carrying `T` or `F`. | Suspended as the primary unit. Replaced by **Evaluable Item (`A`)** indexed by **Boundary (`B`)** and **Inquiry State (`Σ`)** ([`layer1-scope-factorization`](design-review.md#layer1-scope-factorization)); internal grammar of `A` remains open ([`layer5-content-and-coreference`](design-review.md#layer5-content-and-coreference)). | quarantined |
| **Consistency** | Syntactic/semantic absence of deriving `A ∧ ¬A` (tied to classical Explosion). | Suspended until negation is defined ([`layer4-negation-vs-exclusion`](design-review.md#layer4-negation-vs-exclusion)). Use **Collision-Free** (no `(B, A)` holds both `+` and `-` in `Σ`) for local non-clash. | quarantined |
| **Contradiction** | Conjunction `A ∧ ¬A` triggering global Explosion (`Ex Falso Quodlibet`). | Distinguished from **Collision** (co-presence of `+` and `-` on overlapping `B` in `Σ`), which triggers local **Inference Quarantine** and **Revision Obligation** rather than Explosion ([`layer1-collision-quarantine`](design-review.md#layer1-collision-quarantine)). | quarantined |
| **Completeness** | Semantic completeness (`⊨` implies `⊢`) or syntactic completeness (every sentence or its negation is provable, subject to Gödelian limits). | Never use informally to mean "finished." Use **end-to-end** for architectural coverage and **No-Gaps** for epistemic/boundary closure where every item is either `+` or `-`. | quarantined |
| **Validity / Proof** | Classical truth-preservation (`⊨`) or monotone finitary derivation (`⊢`) over static premises. | Deferred until structural consequence and conditional rules are settled ([`layer3-structural-rules-and-cut`](design-review.md#layer3-structural-rules-and-cut), [`layer4-implication-and-curry-barrier`](design-review.md#layer4-implication-and-curry-barrier)). | quarantined |
| **Identity / Object** | Discrete enduring individual (`x`) governed by absolute Leibnizian equality (`x = y`) over a fixed quantifier domain. | Deferred to content grammar and co-reference analysis ([`layer5-content-and-coreference`](design-review.md#layer5-content-and-coreference)). | quarantined |

## 2. Working Primitives & Local Terms

| Term | Operational Definition | Governing Entry | Status |
| :--- | :--- | :--- | :--- |
| **Witness / Grounding (`+`)** | Irreducible positive polarity: an explicit basis, construction, or evidence supporting an evaluable item `A` under boundary `B` in inquiry state `Σ`. | [`layer1-dual-polarity`](design-review.md#layer1-dual-polarity) | decided |
| **Exclusion / Refutation (`-`)** | Irreducible negative polarity: an explicit obstruction, incompatibility, or counterexample ruling out `A` under boundary `B` in inquiry state `Σ`. | [`layer1-dual-polarity`](design-review.md#layer1-dual-polarity) | decided |
| **Domain Boundary (`B`)** | Explicit regime or applicability conditions delimiting where a claim applies; disjoint boundaries coexist without triggering conflict. Formal composition rules are pending ([`layer3-boundary-composition`](design-review.md#layer3-boundary-composition)). | [`layer1-scope-factorization`](design-review.md#layer1-scope-factorization) | decided |
| **Inquiry State (`Σ`)** | Situated state of accumulated witnesses, exclusions, and unresolved obligations that evolves non-monotonically via dynamic updates. | [`layer1-scope-factorization`](design-review.md#layer1-scope-factorization) | decided |
| **Open** | Derived status of `(B, A)` in `Σ`: neither witnessed (`+`) nor excluded (`-`). | [`layer1-dual-polarity`](design-review.md#layer1-dual-polarity) | decided |
| **Grounded** | Derived status of `(B, A)` in `Σ`: witnessed (`+`) and not excluded (`-`). | [`layer1-dual-polarity`](design-review.md#layer1-dual-polarity) | decided |
| **Excluded** | Derived status of `(B, A)` in `Σ`: excluded (`-`) and not witnessed (`+`). | [`layer1-dual-polarity`](design-review.md#layer1-dual-polarity) | decided |
| **Collision** | Derived status of `(B, A)` in `Σ`: both witnessed (`+`) and excluded (`-`) over overlapping boundary `B`. Triggers Inference Quarantine and Revision Obligation rather than Explosion. | [`layer1-collision-quarantine`](design-review.md#layer1-collision-quarantine) | decided |
| **Inference Quarantine** | Local containment rule under which a collided `(B, A)` loses transmission authority and cannot license downstream inferences while its collision remains unresolved. | [`layer1-collision-quarantine`](design-review.md#layer1-collision-quarantine) | decided |
| **Revision Obligation** | Normative tension recorded in `Σ` whenever a `Collision` occurs, requiring discharge via boundary narrowing/splitting or defeat/retraction of a conflicting ground. | [`layer1-collision-quarantine`](design-review.md#layer1-collision-quarantine) | decided |
| **No-Gaps / No-Gluts** | Explicit closure conditions on `(B, Σ)`: **No-Gaps** means no item is `Open` (every item has `+` or `-`); **No-Gluts** means no item is in `Collision`. Used to characterize classical and constructive boundary specializations. | [`scope-anchor-unified-core`](design-review.md#scope-anchor-unified-core) | decided |
