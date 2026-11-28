---
title: Logic Specification Design Review Ledger
status: active
date: 2026-11-25
---

# Design Review Ledger

This register tracks foundational design questions, inherited-assumption audits, and architectural decisions for `unbound-logic/logic-spec`. It is governed by [AGENTS.md](../AGENTS.md) and cross-referenced with [docs/glossary.md](glossary.md).

## Status & Entry Rules

Statuses:
- `open` — problem identified; no resolution ratified yet (`[Exploratory]`).
- `proposed` — candidate resolution drafted and under Socratic / Anti-Triviality stress-testing (`[Exploratory]`).
- `decided` — `[Decided]` by the maintainer, awaiting formal specification in `spec/`.
- `done` — incorporated into ratified `spec/` documents (must name the specification citation and commit).
- `superseded` — replaced by a later entry (must name its successor).

Rules for `decided` entries:
1. **Explicit Date & Ratification**: Record the ratification as `**Decided (Norman, YYYY-MM-DD).**`.
2. **Anti-Triviality & Rejected Alternatives**: State what the choice permits, what it excludes, and which alternatives were rejected and why.
3. **Falsifiable Reopening Condition (`Reopen if:`)**: Every `decided` entry ends with `**Reopen if:**` naming a concrete logical, structural, or epistemic failure condition (e.g., a counterexample, a Curry-style triviality derivation, collapse into an inherited default, or inability to recover a declared boundary case)—never a vague preference.

## 1. Epistemic Foundation & Scope (Layer 8)

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `zetetic-friction-source` | Under a zetetic (Greek *zētētikos*, inquiry-driven) stance that defaults neither to Platonism (a static, mind-independent realm of abstract objects) nor to pure formalism (arbitrary symbol manipulation), what supplies the resistance ("friction") that distinguishes valid moves from arbitrary noise? | **Decided (Norman, 2026-11-25).** Adopt coupled two-axis friction: (1) **Structural Constraint Friction**—invariants of distinction, compatibility, and exclusion that rule out jointly unrealizable configurations without positing Platonic objects; coupled with (2) **Situated Inquiry Friction**—evidential/operational challenge and revision across time for finite, partial inquirers. Permits both strict structural laws and defeasible evidential updates; excludes both arbitrary conventionalism indifferent to clash and timeless deduction severed from partiality and revision. Rejected single-axis alternatives: empirical-only friction (presupposes proto-logical incompatibility to detect clash and under-accounts for formal/counterfactual reasoning), dialogical-only friction (risks social relativism / coherent group delusion), and structural-only friction (risks crypto-Platonism without an anchor for what is constrained). **Reopen if:** Formalizing both axes requires bolting a closed classical deduction engine onto an external belief-revision wrapper with no shared Layer 1 primitives, or the structural axis cannot be stated without presupposing a fixed mind-independent domain of abstract objects. | done: [`core.md`](../spec/core.md) §2 item 7, §3 items 8–10 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `scope-anchor-unified-core` | Should `logic-spec` target exclusively informal/scientific defeasible inquiry, exclusively closed-world formal deduction, or a unified core from which classical and constructive deduction emerge as explicit boundary specializations? | **Decided (Norman, 2026-11-25).** Target a **unified core** whose general regime handles explicit boundaries, partial information, and non-monotonic revision, and whose classical and constructive deductive regimes emerge as explicit boundary-condition specializations (frozen inquiry state `Σ`, single closed boundary `B`, plus No-Gaps and No-Gluts for classical bivalence; No-Gluts and monotone `Σ` for constructive behavior). Excludes ad-hoc dual-engine designs where classical logic is pasted beside an inquiry layer without a derivable specialization path. Rejected narrowing solely to epistemology (weak formal calculability) or solely to closed-world deduction (re-imports Fregean severance from inquiry). **Reopen if:** Deriving classical bivalent consequence under the declared closure conditions (frozen `Σ`, closed `B`, No-Gaps, No-Gluts) requires adding an ad-hoc rule that contradicts or breaks the general core's inference rules. | done: [`core.md`](../spec/core.md) §4 item 13 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `org-charter` | As `unbound-logic` grows beyond `logic-spec`, its design principles are scattered across `AGENTS.md`, this ledger and conversations, so each new repository and collaborator would settle recurring choices anew. A charter proposed from memory showed the risk: it restated the rejected option of [audit-universal-existential-import](design-review.md#audit-universal-existential-import) (empty restricted universals stay `Open`) and cited concepts that no ratified document defines. Should the organization record shared design principles, and in what form? | **Decided (Norman, 2026-11-26).** Adopt the one-page charter v0.1 in `unbound-logic/.github` (`CHARTER.md` at `d5fd80b` there): seven principles (explicit boundaries; situated inquiry with no global view; completeness witnessed, never assumed; evidence reported at its true strength; friction without explosion and revision without escape; idealization with a stated price; specification first with honest projection), each stating what it forbids, a tie-break, its ratified precedents from this ledger and a reopen condition. The principles constrain and audit decisions but do not derive them; a principle without a ratified precedent is not added; changes follow this ledger's process. Each repository's `AGENTS.md` cites the charter and keeps its own guardrails and workflow. *Permits*: consistent tie-breaking across repositories and collaborators, human or AI. *Excludes*: a worldview manifesto, principles written from memory without precedent, and treating the charter as a decision procedure. *Rejected*: a metaphysical mission statement (contradicts the zetetic stance); the proposed draft as written (its uncertainty principle restated the rejected existential-import option, it cited undefined concepts such as atomless regions and an observation operator, and "ontology-first" suggested a Platonist priority); keeping the principles only in each repository's `AGENTS.md` (they would drift apart as repositories multiply). **Reopen if:** a ratified decision cannot be reconciled with any principle, or two repositories ratify conflicting tie-breaks under the same principle. | done: [`AGENTS.md`](../AGENTS.md) §1 (commit "meta: cite the organization charter in AGENTS.md") |

## 2. Primitive Unit & Scope Architecture (Layer 1)

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `layer1-dual-polarity` | Classical propositions (`P`) collapse "not yet refuted" and "positively established" into a single binary truth tag (`T`/`F`), implicitly locking in Excluded Middle and Double Negation Elimination. What should the ground-floor polarity of an evaluable item `A` be? | **Decided (Norman, 2026-11-25).** Adopt two irreducible ground-floor polarities for an evaluable item `A`: **Witness / Grounding (`+`)** (an explicit positive basis, construction, or evidence supporting `A`) and **Exclusion / Refutation (`-`)** (an explicit obstruction, incompatibility, or counterexample ruling out `A`). The four statuses—`Open` (neither), `Grounded` (`+` only), `Excluded` (`-` only), and `Collision` (both `+` and `-`)—are derived from the presence or absence of these two polarities rather than posited as primitive truth values. Acknowledges historical kinship with bilateralism, Belnap-Dunn FDE, and Nelson's N4; differentiation comes from combining dual polarity with [`layer1-scope-factorization`](design-review.md#layer1-scope-factorization) and [`layer1-collision-quarantine`](design-review.md#layer1-collision-quarantine). Rejected single-polarity assertion (erases the zetetic gap between open and grounded), exclusion-only primitives (risk smuggling existence via double negation), and pure update-only primitives without content polarity (risk collapsing into a state machine lacking cross-state invariants). **Reopen if:** Either polarity proves strictly definable from the other without reintroducing double-negation collapse (`¬¬A → A`), or dual polarity cannot support an implication connective without either Curry-style triviality or loss of valid chaining over uncontested claims. | done: [`core.md`](../spec/core.md) §3 item 8 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `layer1-scope-factorization` | Treating scope as an unstructured context tag `C` risks either fragmentation (every claim carries a private `C`, so nothing ever collides) or silently disguising classical premise sets `Γ`. How should scope be structured? | **Decided (Norman, 2026-11-25).** Factor scope into two orthogonal dimensions: **Domain Boundary (`B`)** (the explicit regime and conditions under which a claim applies, allowing disjoint regimes to coexist without conflict) and **Inquiry State (`Σ`)** (the situated evidential/commitment state that evolves non-monotonically over time via dynamic updates). Genuine conflict occurs only when `+` and `-` arise for the same item `A` over overlapping/compatible boundaries `B` within an inquiry state `Σ`. Rejected a single unfactored scope `C` because it conflates disjoint applicability regimes (no revision required) with new counter-evidence inside an overlapping regime (revision required). **Reopen if:** Boundary composition (`B₁ ⊕ B₂`) cannot be formalized without either collapsing `B` back into an unstructured classical premise set `Γ` or allowing arbitrary ad-hoc boundary splitting that lets any claim evade refutation. | done: [`core.md`](../spec/core.md) §2 items 4, 7 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `layer1-collision-quarantine` | When both `+` and `-` hold for `(B, A)` under overlapping `B` at state `Σ` (`Collision`), classical Explosion (`Ex Falso Quodlibet`) trivializes the whole state, whereas passive paraconsistency leaves `-` toothless. How must the system handle `Collision`? | **Decided (Norman, 2026-11-25).** Reject both global Explosion and passive paraconsistency. Adopt **Inference Quarantine + Revision Obligation**: (1) a collided `(B, A)` loses transmission authority and cannot license downstream inferences while collided; and (2) `Σ` records an explicit unresolved tension that must be discharged by narrowing/splitting `B` or defeating/retracting a conflicting ground. Explicitly accepts that Transitivity (`Cut`) and Monotonicity are scoped/defeasible across collided or revisable grounds, requiring provenance/dependency tracking. Rejected Explosion (fragile under localized empirical/inquiry clashes), passive paraconsistency (fails the Anti-Triviality Test because exclusion imposes no operational cost), and strict immediate non-collision (cannot represent legitimate intermediate states of inquiry holding real conflicting evidence prior to resolution). **Amended when formalized (Norman, 2026-11-25):** Stratified Quarantine (`spec/core.md` §3 item 10, `spec/metatheory.md` `MT-1`) uses a Van Gelder alternating fixpoint over obstruction sets paired with Tarjan source-SCC locking of mutual symmetric conflicts so neither defeated derivations nor symmetric conflict cycles emit downstream ghost collisions. **Reopen if:** Quarantine blocks compositional proof over strictly uncontested chains, or provenance and quarantine propagation cannot be specified without reintroducing global Explosion or uncheckable circularity. | done: [`core.md`](../spec/core.md) §3 item 10 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |

## 3. Boundary Algebra & Structural Consequence (Layer 3)

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `layer3-boundary-composition` | What is the formal structure of Domain Boundary `B` (overlap, refinement `B' ⊑ B`, incompatibility), and what anti-immunization constraint prevents arbitrary ad-hoc boundary splitting to dodge refutation? | **Decided (Norman, 2026-11-25).** Treat `B` as a **functional constraint-frame role** (not a separate ontological kind from evaluable items `A`, so a boundary condition in one inquiry can be tested as an item in another) with a meet-semilattice structure: (1) **Refinement (`B' ⊑ B`)** (`B'` is at least as restrictive as `B`); (2) **Overlap / Meet (`B₁ ⊓ B₂`)**, where `+A` on `B₁` and `-A` on `B₂` **must** trigger `Collision` on `B₁ ⊓ B₂` whenever `B₁ ⊓ B₂ ≠ ⊥_B` (disjoint regimes with `B₁ ⊓ B₂ = ⊥_B` coexist without conflict); and (3) **Empty / Impossible Boundary (`⊥_B`)**, which has no realizable domain and **cannot supply a genuine positive Witness (`+`)** (blocking vacuous explosion via impossible boundaries). To counter Popperian ad-hoc boundary splitting, enforce **Non-Erasure Scope-Shrinkage Accounting (M2)**: narrowing `B` to `B'` to re-ground `A` never erases the refutation on `B`; `(B, A)` remains recorded as `Excluded (-)` while `(B', A)` carries explicit narrowing provenance. Explicitly distinguish M2 boundary-narrowing (where the counterexample on `B` remains live) from vertical **Retraction** in `Σ` of a discredited counterexample (e.g., faulty observation), which restores `B` directly without shrinking scope. Content-level non-pointwise splitting admissibility (**M1**, forbidding extensional excision of the counterexample instance alone) is deferred to [`layer5-content-and-coreference`](design-review.md#layer5-content-and-coreference). Rejected unstructured context tags (allow fragmentation to evade collision) and treating `B` as a separate static ontology (prevents putting boundary conditions under scrutiny). **Reopen if:** Meet composition cannot support downward inheritance without collapsing `B` into a classical monotone premise set `Γ`, or M2 plus Layer 5's M1 still permits a systematic stratagem that immunizes arbitrary false generalizations against refutation. | done: [`core.md`](../spec/core.md) §2 items 4, 7, §3 item 9 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `layer3-structural-rules-and-cut` | Under `B × Σ` and [`layer1-collision-quarantine`](design-review.md#layer1-collision-quarantine), which Gentzen structural rules (Reflexivity, scoped `Cut`/Transitivity, Monotonicity/Weakening, Contraction, Exchange) hold strictly, which hold defeasibly, and how does dependency/provenance propagation work when an intermediate node enters `Collision`? | **Decided (Norman, 2026-11-25).** Separate **horizontal** consequence (within a fixed inquiry state `Σ`, across boundaries `B`) from **vertical** evolution (across updates `Σ₀ → Σ₁`): (1) **Reflexivity**: distinguish local ground record (`+`/`-`) from transmission authority; collided items retain records but lose transmission authority. (2) **Monotonicity / Weakening**: strict uncontested grounds inherit downward along compatible non-empty refinements (`B' ⊑ B`, `B' ≠ ⊥_B`), while premise addition that introduces `-` and vertical `Σ` updates are explicitly non-monotonic. (3) **Scoped `Cut` + Well-Founded DAG Provenance**: `Cut` holds strictly along uncontested chains on compatible meets (`B₁ ⊓ B₂ ≠ ⊥_B`), preserving deductive composition; every derived ground carries an **acyclic, well-founded provenance DAG** anchored in base witnesses/exclusions in `Σ` (mutual-support cycles grant zero grounding), so when an intermediate node enters `Collision`, only downstream conclusions lacking an independent uncollided DAG path are automatically quarantined. (4) **Contraction**: retained horizontally for reusable established grounds (placing the Curry Paradox barrier in [`layer4-implication-and-curry-barrier`](design-review.md#layer4-implication-and-curry-barrier)). (5) **Exchange**: holds horizontally within fixed `Σ`; vertical update sequences `Σ₀ → Σ₁ → Σ₂` are non-commutative. (6) **Explosion**: rejected globally in the general core (and holds only vacuously under `No-Gluts` closure in [`scope-anchor-unified-core`](design-review.md#scope-anchor-unified-core)). Rejected bare boolean polarities without provenance (leave ghost conclusions or force Explosion), unconstrained cyclic provenance (allows circular self-grounding to survive Quarantine), and a core-wide contraction-free linear substrate (imposes heavy resource-accounting syntax on reusable inquiry facts). **Reopen if:** Maintaining well-founded DAG provenance makes basic formal derivations intractable or ambiguous under derived connectives, or horizontal Contraction proves incompatible with the Curry barrier chosen in [`layer4-implication-and-curry-barrier`](design-review.md#layer4-implication-and-curry-barrier). | done: [`core.md`](../spec/core.md) §3 items 8, 10–11 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |

## 4. Negation, Implication, Connectives & Self-Reference Barrier (Layer 4)

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `layer4-negation-vs-exclusion` | How does ground-floor Exclusion (`-`) relate to object-level Negation (`¬`), implicative vs. pure cancellation negation (Sanskrit *paryudāsa* vs. *prasajya-pratiṣedha*), and material incompatibility (e.g., incompatible properties without an explicit `¬`)? | **Decided (Norman, 2026-11-25).** Disentangle classical univocal `¬` into three distinct operations plus one boundary-constraint mechanism, all feeding cleanly into ground-floor dual polarity without reintroducing Excluded Middle or Explosion: (1) **Strong Polarity Flip (`~A`, akin to Sanskrit *paryudāsa* / strong bilateral negation)**: `+(~A) ⟺ -A` and `-(~A) ⟺ +A` (involutive on polarities without forcing `A ∨ ~A` on `Open` items or Explosion on `Collision`). (2) **Pure Cancellation / Retraction (`Retract` in `Σ`, akin to Sanskrit *prasajya-pratiṣedha*)**: defeating or withdrawing an unsupported ground or defective refutation is an inquiry-state update returning `(B, A)` toward `Open`—never modeled as `-(~A)`—blocking the fallacy that discrediting a refutation establishes `+A`. (3) **Structural Impossibility (`A → ⊥`, equivalently `B ⊓ [A] = ⊥_B` where `⊥` is the unsatisfiable item having no witness on any non-empty boundary)**: deriving boundary collapse from assuming `A` induces `-A`, while refuting impossibility (`(A → ⊥) → ⊥`) does **not** produce a positive witness `+A` (no Double Negation Elimination). (4) **Material Incompatibility (`A ⊥_B C`)**: declared mutual-exclusion constraints inside boundary `B`, whereby `+A` automatically derives `-C` (with provenance pointing to `+A` and `A ⊥_B C`) and symmetrically `+C` derives `-A`, unifying material and formal opposition under Exclusion (`-`). Rejected a single overloaded negation operator (conflates active refutation with mere withdrawal and sneaks in Double Negation Elimination). **Amended (Norman, 2026-11-25):** Explicit counterexample exclusion of conditionals (`B ⊩⁻ (A → C)`) in `UL-Core` is one-way (`+A ∧ -C ⇒ -(A → C)`), and `imposs-excl` (`+(A → ⊥) ⇒ -A`) is explicitly barred from inverting `-(A → ⊥)` into `+A`; extensional collapse of `-(A → ⊥)` to `+A` holds strictly under atomic-generated `UL-Classical` closure (`No-Gaps` + `No-Gluts`). Additionally, material incompatibility `A ⊥_B C` inherits downward across every non-empty sub-boundary `B' ⊑ B`. **Reopen if:** Interaction between `~A` and `A → ⊥` allows deriving `+A` solely from the failure or non-existence of a refutation, or material incompatibility `A ⊥_B C` requires rules incompatible with [`layer3-boundary-composition`](design-review.md#layer3-boundary-composition). | done: [`core.md`](../spec/core.md) §2 item 7, §3 item 12 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `layer4-implication-and-curry-barrier` | How is conditional/entailment (`→` / `⊢`) defined over dual polarities and `B × Σ`, and where does the load-bearing barrier against Curry's Paradox sit under self-reference? | **Decided (Norman, 2026-11-25).** Define **Scoped Conditional (`A → C` on boundary `B`)** with dual polarity: (1) **Witness `+(A → C)` on `B`**: a verified transmission/construction mapping any unquarantined `+A` on any non-empty sub-boundary `B' ⊑ B` to `+C` on `B'` (recording provenance dependency on `+A` and `+(A → C)`), eliminating vacuous `False → anything` witnesses in the general core while ensuring Quarantine propagates through Modus Ponens; and (2) **Exclusion `-(A → C)` on `B`**: exhibiting a direct counterexample on a non-empty sub-boundary `B' ⊑ B` where `+A` and `-C` hold (which recovers classical material implication `-A ∨ +C` automatically under frozen `Σ`, atomic closed `B`, `No-Gaps`, and `No-Gluts`). Because horizontal Contraction ([`layer3-structural-rules-and-cut`](design-review.md#layer3-structural-rules-and-cut)) plus Modus Ponens plus Conditional Introduction (`→I`) allows a finite, acyclic 7-step derivation of Curry's Paradox (`K ≡ (K → Z) ⊢ Z`) that acyclic provenance DAGs alone **cannot** block, adopt **Stratified / Stage-Indexed Reflection + Strictly Positive / Well-Founded Definitions** as the Curry firewall: every reflection or grounding predicate over level `n` (or inquiry state `Σ_t`) enters strictly at level `n+1` (or `Σ_{t+1}`), and recursive item definitions prohibit unguarded negative/implicational self-reference (forbidding same-stage `K_n ≡ (K_n → Z)`). Rejected relying on acyclic provenance alone (provably bypassed by the finite Curry derivation), dropping `→I` / Deduction Theorem (cripples standard proof-by-assumption), and reopening Contraction into a fully linear core (excessive ceremony for reusable facts). **Amended when formalized (Norman, 2026-11-25):** To preserve symmetric downward heredity and prevent counterexamples on a sub-boundary `B₂` from leaking onto disjoint sibling regimes `B₁`, `B ⊩⁻ (A → C)` is introduced locally by `B ⊩⁺ A` and `B ⊩⁻ C`; any counterexample on a non-empty sub-boundary `B' ⊑ B` yields `B' ⊩⁻ (A → C)`, colliding on `B'` and triggering upstream obstruction/quarantine of `(B, +(A → C))` (`spec/core.md` §3 items 9–10, 12). **Amended when formalized (Norman, 2026-11-25):** Because Glivenko's theorem (`(((P ∨ (P → ⊥)) → ⊥) → ⊥)`) is provable in `UL-Minimal` and combining `imposs-excl` with a biconditional `-(A → C) ⟺ +A ∧ -C` would invert into `+(P ∨ (P → ⊥))` (LEM) and DNE, conditional exclusion in `UL-Core` is strictly one-way (`+A ∧ -C ⇒ -(A → C)`), scoping the `-(A → C) ⟺ +A ∧ -C` biconditional solely to atomic-generated `UL-Classical` states (`No-Gaps` + `No-Gluts`). Additionally, local assumptions inside `→I` sub-proof boxes are lexically scoped and do not collide with ambient `B ⊩⁻ A` (preserving `A → A` and constructive weakening `C ⊢ A → C` without exploding from `-A`), and cross-stage reflection reads frozen `#stageArchive` snapshots isolating both `Σ` entries and `BoundarySystem` metadata from later mutations (`spec/core.md` §1 item 3). **Reopen if:** A Curry-style triviality derivation succeeds across stratified stages or via boundary reflection, or strict positivity + stage stratification blocks a legitimate self-referential reasoning pattern essential to general inquiry that cannot be faithfully expressed across stages `Σ_t → Σ_{t+1}`. | done: [`core.md`](../spec/core.md) §1 item 3, §3 items 10, 12 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |
| `layer4-conjunction-disjunction-and-covers` | How are Conjunction (`A ∧ C`) and Disjunction (`A ∨ C`) witnessed and excluded under `B × Σ`—specifically, does `+(A ∨ C)` on `B` require a uniform witness across all of `B` (strict constructive disjunction property) or permit exhaustive boundary-partition covers (`B = B₁ ⊔ B₂` with `+A` on `B₁` and `+C` on `B₂`), and how does this affect `No-Gaps` on non-atomic boundaries? | **Decided (Norman, 2026-11-25).** Define dual-polarity **Conjunction (`A ∧ C` on `B`)**: `+(A ∧ C)` holds iff both `+A` and `+C` hold unquarantined on `B` (joining their provenance DAGs, so a collided conjunct quarantines dependent conclusions without Explosion); `-(A ∧ C)` holds iff `-A` or `-C` holds on `B`. Define **Explicit Cover-Witnessed Disjunction (`A ∨ C` on `B`, Beth / sheaf style)**: `-(A ∨ C)` holds iff both `-A` and `-C` hold on `B`; `+(A ∨ C)` holds on `B` iff there exists an **explicit, witnessed finite exhaustive cover** `{B₁, ..., B_k}` of `B` (`B = ⨆ B_i`) such that on each non-empty cell `B_i`, either `+A` or `+C` is witnessed. Cover exhaustiveness (`B = ⨆ B_i`) must itself be a witnessed structural relation (blocking incomplete covers that silently drop cases). When `k = 1`, this reduces to direct uniform witness; when `k > 1`, it supports case analysis (e.g., `Even(x) ∨ Odd(x)` on `ℤ = Even ⊔ Odd`) and `∨E` gluing while still refusing `+(A ∨ ~A)` on `Open` items lacking an actual cover. Rejected strict uniform-only disjunction (cannot witness basic boundary partitions like `Even ∨ Odd` and breaks `No-Gaps` recovery on non-atomic boundaries). **Amended when formalized (Norman, 2026-11-25):** Added **Standalone Cover-Gluing** (`Sheaf Gluing`): across any witnessed exhaustive cover `{B_i} ▷ B`, uniform `Live` polarity `B_i ⊩± E` glues to `B ⊩± E` while respecting sub-boundary Quarantine obstruction (`spec/core.md` §3 item 12, `spec/metatheory.md` `MT-5`). **Reopen if:** Witnessed finite covers cannot compose stably under boundary meets (`B₁ ⊓ B₂`) without breaking `∨E` gluing or permitting an ungrounded `Open` item to fabricate `+(A ∨ ~A)`. | done: [`core.md`](../spec/core.md) §2 item 5, §3 item 12 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |

## 5. Content Grammar, Co-Reference & Anti-Immunization (Layer 5)

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `layer5-content-and-coreference` | What is the internal grammar of an evaluable item `A` beyond opaque propositional atoms, how is co-reference preserved across boundary refinement (`B → B'`) and inquiry updates (`Σ₀ → Σ₁`) without equivocation, and how is content-level non-pointwise boundary splitting (**M1**) formally constrained? | **Decided (Norman, 2026-11-25).** Adopt **Relation-First Role-Indexed Grammar (G3)** with four components: (1) **Role-Indexed Relational Claims (`R(r₁: t₁, ..., r_n: t_n)`)**: atomic items assert relations, configurations, or transformations over role-labeled handles (unary properties `P(x)` are the 1-ary special case; processes and relations are first-class without Aristotelian substance bias). (2) **Boundary-Scoped Equivalence (`t₁ ≈_B t₂`) & Anti-Equivocation**: sameness is a witnessed congruence relation respecting all relations native to `B`, allowing macroscopic vs. microscopic granularities (`B_macro` vs. `B_micro`) to coexist without contradiction; handles carry explicit boundary-relative individuation criteria `I_B(t)` so cross-update (`Σ₀ → Σ₁`) evidence binds to `(B, A(t))` only when `t' ≈_B t` is witnessed under `I_B`. (3) **Boundary-Scoped Quantifiers (`∀(x : B) A(x)` and `∃(x : B) A(x)`)**: no pre-completed cosmic domain `D`; `+∃` requires a concrete admissible witness handle `w` in `B` with `+A(w)`; `-∀` requires a concrete counterexample `w` in `B` with `-A(w)`; `+∀` requires generic structural grounding over arbitrary admissible `x : B` (or an exhaustive cover of `B`). (4) **Formalized Anti-Immunization (M1)** (paired with Layer 3's M2 Non-Erasure): after `-A(w)` on `B`, an admissible boundary refinement `B' = B ⊓ [δ]` must satisfy **(i) Non-Circularity** (`δ(x)` cannot reference `A(x)` directly or indirectly) and **(ii) Non-Contingent Structural Definability** (`δ(x)` cannot excise `w` merely by its contingent empirical handle tag such as `x ≉ specimen_402`, while permitting structurally defined singularities of `B`'s own operations such as the additive identity `0` in `ℝ \ {0}`). Rejected standard FOL over a fixed cosmic domain `D` with absolute `=` (re-imports substance/Platonist inertia), pure morphism-only syntax (overly indirect for situated empirical/inquiry claims), and naive M1 forbidding all point exclusions (falsely outlaws algebraic singularities like `ℝ \ {0}`). **Amended when formalized (Norman, 2026-11-25):** Formalized **open-domain schematic `∀I` / `∃E`** with capture-avoiding α-substitution and bound-variable freshness (`spec/core.md` §3 item 12), engine-side `≈_B` congruence closure (`refl`/`sym`/`trans`) and `∀E` / `domainConstraint [δ]` evaluation, and **`M1(iii)` Independent Excess-Content Witness** (requiring a `Live +δ(u)` witness on a non-refuted surviving handle and blocking `-δ(v)` survivors when contingent handles are excised), bounded by `MT-7`'s **`Formal Horizon Corollary`** on synthetic and honest co-extensional proxies. **Reopen if:** Boundary-relative congruence `≈_B` fails to preserve substitution stability across downward refinement `B' ⊑ B` without leaking equivocation, or refined M1 still allows an arbitrary contingent exception to be disguised as a structural criterion. | done: [`core.md`](../spec/core.md) §1 item 1, §2 items 6–7, §3 item 12 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |

## 6. Boundary Specializations & Deductive Recovery (Layer 2)

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `layer2-classical-boundary-recovery` | Prove or formally demonstrate that under [`scope-anchor-unified-core`](design-review.md#scope-anchor-unified-core) (frozen `Σ`, closed `B`, No-Gaps, No-Gluts), classical bivalent consequence (including `~`, `→`, `∧`, `∨`, and vacuous Explosion) emerges cleanly from the general core without ad-hoc rules. | **Decided (Norman, 2026-11-25).** Establish a four-tier specialization hierarchy derived solely by explicit closure conditions on `(B, Σ)` with no conflicting rules added to the general core: (1) **`UL-Core`** (general dynamic regime: dual polarity `+`/`-`, `B × Σ`, Quarantine, Well-Founded DAG Provenance, Scoped Cut, Stratified Reflection + Strict Positivity). (2) **`UL-Minimal`**: restrict `Σ` to monotone growth (no `Retract`) + **`No-Gluts`** (zero Collisions, so Quarantine never fires and Scoped Cut becomes unrestricted Cut), recovering minimal constructive logic (with strong negation `~` alongside `A → ⊥`). (3) **`UL-Intuitionistic`**: `UL-Minimal` + boundary axiom **`⊥ → C`** (Ex Falso for `⊥`, safe under `No-Gluts` since `⊥` has no witness on any non-empty `B`), recovering Heyting Intuitionistic FOL with Beth cover semantics via [`layer4-conjunction-disjunction-and-covers`](design-review.md#layer4-conjunction-disjunction-and-covers). (4) **`UL-Classical`**: freeze `Σ`, restrict to a closed atomic boundary `B* ≠ ⊥_B` (or a finite cover of atomic cells) with finest congruence `≈_{B*}`, **`No-Gluts`**, **`No-Gaps`**, and level `n = 0`. Under these conditions: `~A` and `A → ⊥` collapse identically to Boolean `¬A` (with Double Negation Elimination); `No-Gaps` closes non-counterexampled `A → C` to `+` (recovering classical material implication `-A ∨ +C`) while `No-Gluts` ensures Modus Ponens never fires on `-A`; `∧`, `∨` (via D2), `∀`/`∃` (over `Dom(B*)`), and `≈_{B*}` recover classical truth tables, Excluded Middle (`A ∨ ~A`), De Morgan quantifier duality, and Leibnizian equality `=`; and classical Explosion (`A, ~A ⊢ C`) holds vacuously under `No-Gluts`. **Reopen if:** Formalizing the derivation calculus in `spec/core.md` uncovers a classical FOL theorem or intuitionistic theorem that fails under the declared closure conditions without modifying `UL-Core`'s general rules. | done: [`core.md`](../spec/core.md) §4 item 13 (commit "spec: add UL-Core formal specification (spec/core.md v0.1.0)") |

## 7. Open Design Problems

No Phase 1 (Layers 1–8) question remains open. The entries below were found on 2026-11-25 by a Claude Code audit of `spec/` against the reference kernel at commit `785b74e`, using read-only probes. Implementation entries state a reproduction, with an executable snippet for each under [Audit Reproductions](design-review.md#audit-reproductions); claim and governance entries cite the passages concerned. The maintainer ratified a resolution for each on 2026-11-25 (`decided`); each closes as `done` once the specification and kernel changes land. `audit-metatheorem-overclaim` closed as `done` on 2026-11-26. `audit-universal-existential-import` was found later, during the maintainer's review of the MT-9 proof at commit `7fd4c6d`, and was ratified on 2026-11-26 (`decided`). The entries from `audit-unverified-cover-authority` on were raised by an external review of commit `dfa0fb9` on 2026-11-27 and reproduced against the kernel at commit `2713cba` with read-only probes (`audit-terminology-drift` also records drift found while checking it). The maintainer ratified a resolution for each on 2026-11-28 (`decided`).

| Key | Problem | Resolution | Status |
| :--- | :--- | :--- | :--- |
| `audit-m1-criterion-decoupling` | **The M1 splitting criterion `δ` is not bound to the refined boundary `B'`.** `core.md` §2 item 7 defines `RefineBoundary(B → B' = B ⊓ [δ])`, but `refineBoundary` in [`src/engine.ts`](../src/engine.ts) never checks that `Dom(B')` consists of the handles of `B` that satisfy `δ`: `B'` is fixed beforehand by `defineBoundary` (`handles` / `handleFilter`), and `δ` is only screened by M1(i)–(iii). Reproduction: boundary `Swan` with contingent handles `swan_402`, `swan_101`; `Swan_Rest ⊑ Swan` drops `swan_402` via `handleFilter`; `Observe⁻(Swan, White(swan_402))`, `Observe⁺(Swan, Feathered(swan_101))`, `Observe⁺(Swan, Feathered(swan_402))`; `refineBoundary(Swan → Swan_Rest)` with `δ := Feathered(x)` returns `ok: true` although the excised counterexample itself satisfies `δ` (`Live +Feathered(swan_402)`). Any predicate unrelated to the split that has one surviving positive witness therefore licenses excising a counterexample, which is the immunization M1 exists to block. The ratified Swan example ([`test/boundary-and-inquiry.test.ts`](../test/boundary-and-inquiry.test.ts), Attempt 3) likewise never establishes that `swan_402` fails `~Habitat(x, Australia)`. Separately, M1(i) forbids `δ` referencing `A` "directly or indirectly", but the kernel checks only direct relation names (`collectRelations(criterionItem).has(targetRelation)`), so dependence routed through a registered incompatibility or conditional is not detected. Affects `metatheory.md` MT-7. Executable reproduction: R1 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-25).** Bind `δ` to `B'` by verification: `RefineBoundary(B → B')` is admitted only if `Dom(B') = {h ∈ Dom(B) : ¬Live −δ(h)}` and every handle excised from `Dom(B)` carries a `Live −δ(h)` witness on `B`, in addition to M1(i)–(iii) and M2. Handles whose `δ` is `Open` stay in `B'`; a later `Live −δ(v)` on a surviving handle `v` records a revision obligation against the refinement. The "indirect" reference of M1(i) is checked as reachability from the relations of `δ` to the target relation in a relation-dependency graph built from `C_B` (incompatibilities and structural collapses) and the `Live` conditionals of `Σ`. *Permits*: refinements whose criterion is shown, by independent evidence, to separate every excised handle, including under partial information about the survivors. *Excludes*: decorative criteria that the excised counterexample satisfies or was never tested against (R1), and aliases of the target relation routed through registered links. *Rejected*: having the engine construct `B'` from `δ` (the same guarantee for M1, but `B'` also carries parents, native relations and meets that the engine would have to invent, and the kernel API would break); requiring `Live +δ` on every survivor (makes refinement nearly impossible under partial information, while the burden of evidence belongs on the excised handles). Impact measured at `785b74e`: 4 of 40 tests lack the separating observation in their fixtures. **Reopen if:** a criterion that an excised handle satisfies, or that was never tested against it, is still admitted (R1 passing after the change), or the reachability check rejects the ratified `ℝ \ {0}` refinement of [worked-examples.md](../spec/worked-examples.md) §2. | done: [`core.md` §2](../spec/core.md#2-boundary-algebra--inquiry-state-dynamics) item 7, M1(i) and M1(iv); [`metatheory.md`](../spec/metatheory.md) MT-7 (commit "feat: bind M1's splitting criterion to the refined domain", commit "spec: specify M1 domain binding and indirect reference") |
| `audit-cover-non-vacuity-drift` | **Registered covers are not re-validated when the boundary system grows, and `C_B` cannot be revised.** `registerCover` in [`src/boundary.ts`](../src/boundary.ts) checks Refinement and Non-Vacuity only at registration, and `witnessedCoversOf` silently skips a Meet-Stability pullback that comes out empty instead of reporting that the cover is not exhaustive (Axioms 3 and 5 of `core.md` §2 item 5 together forbid a non-empty `B' ⊑ B` disjoint from every cell). Reproduction: `C1, C2 ⊑ B` declared disjoint, `WitnessCover({C1, C2} ▷ B)`, then `B3 ⊑ B` declared disjoint from `C1` and `C2`; `isWitnessedCover(B, [C1, C2])` stays `true`. With `Observe⁺(C1, P)` and `Observe⁺(C2, Q)`, `(B3, P ∨ Q)` is `Grounded` while `(B3, P)` and `(B3, Q)` are both `Open`; adding `Observe⁻(B3, P)` and `Observe⁻(B3, Q)` puts `(B3, P ∨ Q)` into `Collision` and records `Rev(B3, P ∨ Q)` although neither disjunct collides on any boundary. The MT-5 proof sketch in `metatheory.md` relies on exactly this Non-Vacuity step. Because `Retract` removes only base observations from `G⁺ ∪ G⁻` and no transition withdraws a cover or incompatibility from `C_B`, the obligation cannot be discharged at its actual source, only by retracting correct observations. Executable reproduction: R2 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-25).** Re-validate every registered cover whenever the boundary system changes (`defineBoundary`, `declareDisjoint`, `defineMeet`). A cover `{B_i} ▷ B` with a non-empty `B' ⊑ B` disjoint from every cell becomes **invalid**: it no longer witnesses `D2` disjunction, `∨E` or Cover-Gluing, grounds derived through it lose that support, and a revision obligation on the cover is recorded. Where the meet of `B'` with a cell is unknown under [audit-unregistered-meet-closed-world](design-review.md#audit-unregistered-meet-closed-world), the cover is **unverified**: it records an obligation without being invalidated. Add a fifth vertical transition `Withdraw(c)` that removes a cover, incompatibility or structural collapse from `C_B` by pure cancellation, so constraints carry identifiers and MT-6 extends to `C_B`. *Permits*: later structure refuting an earlier exhaustiveness claim, and revising a faulty constraint at its source. *Excludes*: covers that stay authoritative after being shown non-exhaustive (R2), and obligations that can be discharged only by retracting correct observations. *Rejected*: refusing the boundary change that breaks a cover (it would make an earlier structural claim immune to later discovery, the immunization M1 and M2 forbid for empirical claims, and the final state would depend on whether the cover or the boundary came first, breaking the order independence observed for observations). **Refined (Norman, 2026-11-26), after the clean-room oracle's reading A37.** Two covers that are each not invalid can compose by Transitivity into a cover that a sub-boundary refutes, whose base change to it is the empty family that Axiom 5 forbids. Derived covers are judged by the same validity rule as registered ones, and an invalid derived cover is not derived, so the closure never yields `∅ ▷ B'`. No separate obligation is recorded: the registry admits no non-empty common sub-boundary of two disjoint boundaries and keeps every registered meet the greatest lower bound of its pair (refined under [audit-unregistered-meet-closed-world](design-review.md#audit-unregistered-meet-closed-world) on 2026-11-28), so covers derived from valid registered covers are valid, and an invalid derived cover comes only from an unverified registered cover, which already carries one. *Rejected*: an evaluation error for such a state (one declaration could make a whole inquiry state unevaluable); inferring in item 4 that a boundary disjoint from every cell of a witnessed cover of `C` is disjoint from `C` (closest to the intended meaning, but disjointness and cover validity would then depend on each other, through a fixpoint that need not be unique). **Reopen if:** re-validation makes two orderings of the same boundary definitions and cover registrations end in different evaluation results, or invalidation removes a ground that has an independent derivation not passing through the invalid cover. | done: [`core.md`](../spec/core.md#2-boundary-algebra--inquiry-state-dynamics) §2 items 5 and 7 (cover validity, `Withdraw`), §5 item 14; [`metatheory.md`](../spec/metatheory.md) MT-5, MT-6 (commit "feat: re-validate covers and withdraw constraints from C_B", commit "spec: specify cover validity, Withdraw and the two status axes", commit "feat: judge derived covers and base-change them in the cover closure", commit "spec: judge derived covers by the validity rule of item 5") |
| `audit-unregistered-meet-closed-world` | **Absence of a registered common sub-boundary is read as disjointness.** `BoundarySystem.meet` in [`src/boundary.ts`](../src/boundary.ts) returns `⊥_B` whenever two boundaries have no explicit meet, no declared disjointness, and no registered common sub-boundary, and it throws `Ambiguous meet` when several maximal candidates exist, so `⊓` is not total. Reproduction: `Lab` and `Field` under `⊤_B`; `Observe⁺(Lab, P)` and `Observe⁻(Field, P)` yield no `Collision`; merely defining `LabField` with parents `Lab` and `Field` then produces one. `core.md` §2 item 4 states a bounded meet-semilattice in which two boundaries overlap iff `B₁ ⊓ B₂ ≠ ⊥_B`, and does not declare this closed-world default, which the Anti-Inertia Audit in [AGENTS.md](../AGENTS.md) §2 requires to be flagged. It also bears on MT-4 in `metatheory.md`, whose disjointness premise can then hold by omission rather than by declaration. Executable reproduction: R3 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-25).** Read the boundary registry open-world: the meet of two boundaries is *overlapping*, *disjoint* (declared, or inherited from declared ancestors), or *unknown*. Unknown overlap never produces `Collision` and never satisfies a disjointness premise (MT-4 requires declared disjointness), and `+A` and `−A` on boundaries whose overlap is unknown record an `OverlapUnknown(B₁, B₂, A)` revision obligation. Several maximal common sub-boundaries still require `defineMeet`. core.md §2 item 4 states the three-valued meet explicitly. *Permits*: boundary systems that grow during inquiry without silently hiding conflicts. *Excludes*: treating an unregistered overlap as evidence of disjointness (R3). *Rejected*: keeping the closed-world default with documentation (honest, and appropriate for a boundary system fixed in advance, but it keeps conflicts invisible until the registry is complete and, combined with cover re-validation, would invalidate a cover every time a sub-boundary is added without registering its meets with the cells). Impact measured at `785b74e`: 5 of 40 tests (one deterministic test and four fuzz generators) rely on implicit disjointness and must declare it. **Refined (Norman, 2026-11-28), after the clean-room oracle's reading A39.** The registry accepted a registered meet that some common sub-boundary of its pair did not lie below, so a valid cover could base-change into an invalid one with no obligation. A registered meet is the greatest lower bound of its pair: every boundary that refines both members is inferred to refine the meet, held to domain monotonicity and to declared disjointness, and a meet whose inferred refinements would break either is refused. Registering a meet thus still settles an ambiguity among several maximal common sub-boundaries. *Rejected*: refusing a meet that existing common sub-boundaries do not lie below, and a boundary below both members but not below their meet (approved and replaced the same day: refinement is fixed when a boundary is defined, so an ambiguity could never be settled once its maximal common sub-boundaries exist); a revision obligation for every invalid derived cover (leaves the faulty meet itself unreported). **Reopen if:** the maintainer adopts boundary systems that are complete by construction, or a ratified worked example needs disjointness that follows from the boundaries' definitions but cannot be expressed by declaration. | done: [`core.md` §2](../spec/core.md#2-boundary-algebra--inquiry-state-dynamics) items 4, 5 and 14 (three-valued meet, Meet-Stability across an unknown overlap, `OverlapUnknown`); [`metatheory.md`](../spec/metatheory.md) MT-4 (commit "feat: read the boundary registry open-world with a three-valued meet", commit "spec: specify the three-valued meet and OverlapUnknown", commit "feat: refuse meets and cover base changes across an unknown overlap", commit "spec: block Meet-Stability across an unknown overlap", commit "feat: keep registered meets as greatest lower bounds by inferred refinement", commit "spec: make a registered meet the greatest lower bound of its pair") |
| `audit-status-obstruction-mismatch` | **`statusOf` reports `Grounded` for an obstructed ground.** `core.md` §3 item 8 defines `Grounded` as at least one valid `π⁺`, no valid `π⁻`, and unobstructed on sub-boundaries. In the [`audit-cover-non-vacuity-drift`](design-review.md#audit-cover-non-vacuity-drift) reproduction, `EvaluationSnapshot.statusOf(B, P ∨ Q)` in [`src/engine.ts`](../src/engine.ts) returns `Grounded` while `isObstructed(B, P ∨ Q)` is `true` and `isLive(B, "+", P ∨ Q)` is `false`. Either the status definition or the kernel API must change so that a caller reading `statusOf` cannot mistake an obstructed ground for a transmission-authorized one. Executable reproduction: R2 under [Audit Reproductions](design-review.md#audit-reproductions) (final three assertions). | **Decided (Norman, 2026-11-25).** Split the reported status into two axes: `localStatus` (`Open`, `Grounded`, `Excluded`, `Collision`, from the ground records on `(B, A)` alone) and `authority` (`Live`, `Quarantined`, or `Undetermined` under the evaluation program of [audit-spec-kernel-coupling](design-review.md#audit-spec-kernel-coupling)). core.md §3 item 8 drops the "unobstructed" clause from the local statuses, and the kernel replaces `statusOf` with an accessor for each axis. *Permits*: reading raw ground records and transmission authority separately. *Excludes*: a status value that a caller can mistake for authorization. *Rejected*: a fifth status value such as `Obstructed` (with a third authority value, one enumeration would need several extra values to keep the polarity of an obstructed ground, and existing comparisons against `Grounded` would silently change meaning). **Reopen if:** a rule or transition in core.md needs a combination of local status and authority that the two axes cannot express. | done: [`core.md`](../spec/core.md#3-dual-polarity-semantics-provenance--derivation-calculus) §3 item 8 (local status and authority as two axes); the kernel reports `localStatus` and `authorityOf` (commit "feat: rename statusOf to localStatus", commit "spec: specify cover validity, Withdraw and the two status axes") |
| `audit-evidence-label-integrity` | **`Consensus` is satisfied by the presence of a test-function name, and one label conflates ratification with evidence.** [AGENTS.md](../AGENTS.md) §2 item 5 defines `[Consensus]` as ratification by the maintainer, but `.spec-guard.json` configures `Consensus` with `evidence: test`, which `spec-guard claims` accepts whenever an `@assert-count` directive counts at least one occurrence of the text `function test_…` in a test file. `spec-guard prove` then shows only that each such rule fails when that text is removed in memory: it does not mutate or fault-inject the kernel, and nothing checks what the named test asserts or that it exercises the claim. At commit `785b74e` the 26 claims read `Consensus 26, Exploratory 0`, their 73 directives name 33 distinct test functions, and this section read "None currently open". The Verification section of [README.md](../README.md) describes this gate as "mutation resistance" and as a "Mutation/fault-injection proof verifying every `@assert-count` rule catches failing implementations", which misstates what it checks. No label separates a maintainer decision (`Decided`), behavior exercised by tests (`Tested`), and a result with a proof (`Proved`), so [metatheory.md](../spec/metatheory.md) presents MT-1–MT-9 as theorems "anchored to executable tests" on the strength of named tests alone. Affects every labelled claim in [core.md](../spec/core.md), [worked-examples.md](../spec/worked-examples.md) and [metatheory.md](../spec/metatheory.md), plus the README Verification section. | **Decided (Norman, 2026-11-25).** Replace `Consensus` / `Exploratory` with a single ladder in which each label implies the one before it: `Exploratory` (under debate), `Decided` (ratified by the maintainer), `Tested` (decided and exercised by a bound behavioral test), `Proved` (tested and backed by a written proof, cited with `Proof:`, that the maintainer has reviewed). Definitions top out at `Tested`. [AGENTS.md](../AGENTS.md), `.spec-guard.json` and `.spec-graph.json` adopt the ladder; every claim is relabelled to the evidence it has; claims receive stable identifiers and test functions are split so that each binding names a test about its claim; README describes `spec-guard prove` accurately; kernel mutation testing runs as a reported metric, not a gate. Continuous integration runs `npm run verify` on every push and pull request, with long fuzzing and mutation runs on GitHub-hosted runners through `workflow_dispatch`. *Permits*: readers to tell a ratified decision from tested behavior and from a proved result. *Excludes*: labels that claim more evidence than exists. *Rejected*: two independent axes (more expressive, but spec-guard holds one label per claim and composite labels would multiply); keeping `Consensus` and adding only `Proved` (leaves the conflation this entry records). Tooling can check only that a proof is cited, not that it is correct. **Reopen if:** a claim needs to be `Proved` without being `Decided`, a ratified definition needs a status the ladder cannot express, or spec-guard cannot enforce a label's requirement as configured. | decided |
| `audit-metatheorem-overclaim` | **MT-8 and MT-9 claim more than their proof sketches and the kernel's finite semantics support.** MT-8 in `metatheory.md` is titled "Soundness & Syntactic Completeness" and states that `UL-Intuitionistic` "yields Heyting Intuitionistic First-Order Logic (`NJ`) under finitary Beth-cover semantics", but its proof sketch shows only that Quarantine never triggers under `No-Gluts` and that `A ∨ ~A` and `(A → ⊥) → ⊥ ⊢ A` are not derivable on an `Open` item; it gives no completeness argument in any direction (every `NJ` theorem derivable, every derivable item an `NJ` theorem, or semantic completeness). The kernel evaluates over finite boundary systems with finite handle domains, and intuitionistic first-order logic is not complete for Kripke or Beth models on finite frames: the double-negation shift `∀x ¬¬A(x) → ¬¬∀x A(x)` holds in every such model yet is not provable in `NJ`, so a semantic completeness claim must either admit infinite structures or be restricted. MT-9 and `core.md` §4 item 13 present the `UL-Classical` result as classical first-order recovery and a "Tarskian classical first-order valuation", but it is defined only over a closed finite `Dom(B*)` or a finite atomic cover, which yields finite-domain classical semantics; validity over finite structures differs from first-order validity (Trakhtenbrot's theorem). The MT-9 proof also restates the truth tables through the `No-Gaps` closure of non-refuted conditionals, so it shows that closure is consistent rather than recovering classical logic independently. Affects MT-8, MT-9, core.md §4 item 13, and the scope sentence of `README.md`. | **Decided (Norman, 2026-11-25).** Split MT-8 into MT-8a (`Tested`): the proof checker implements the rule schemas of `NJ_min` and `NJ` and separates them by `⊥E`, and Quarantine never triggers under `No-Gluts`; and MT-8b (`Exploratory`): soundness of theorems recorded into the engine with respect to engine evaluation. Withdraw the completeness claim and record why: intuitionistic first-order logic is not complete for Kripke or Beth models on finite frames (double-negation shift). Rescope MT-9 and core.md §4 item 13 to finite-domain classical semantics: state the `UL-Classical` closure conditions explicitly, including the conditional closure and the finite-domain quantifier closure, and attach a written proof that the maintainer reviews before MT-9 becomes `Proved`. README's scope sentence follows. *Permits*: metatheorems whose scope matches the kernel's finite semantics. *Excludes*: completeness or full first-order recovery claimed without proof. *Rejected*: relabelling the v0.2.0 statements `Exploratory` without rescoping them (it would leave statements that fail on finite frames inside the normative text). **Reopen if:** a completeness proof for a stated semantics is supplied, or the kernel gains a semantics over infinite structures that the rescoped statements no longer describe. | done: [`metatheory.md` §5](../spec/metatheory.md#5-four-tier-specialization--finite-domain-classical-valuation) MT-8a, MT-8b, MT-9, MT-9b; [`core.md` §4](../spec/core.md#4-boundary-specialization-theorems) item 13; [`README.md`](../README.md) (commit "spec: adopt the claim status ladder, relabel claims, and rescope MT-8 and MT-9", commit "spec: revise MT-9 after review and add MT-9b", commit "docs: align README with the claim ladder, prove semantics, and CI") |
| `audit-spec-kernel-coupling` | **The core `Live` / `Collision` semantics is defined by the kernel, not by the specification.** [core.md](../spec/core.md) §3 item 10 gates every transmissive rule on `Live`, while `Live` depends on `Collision`, which depends on the entries those rules produce; the item settles this circularity only by naming a mechanism ("realized via an alternating fixpoint over obstruction sets"), not by defining it. MT-1 in [metatheory.md](../spec/metatheory.md) proves a least-fixpoint result for an operator `F_Σ` that treats `Entries(Σ)` and `obstructed_Σ` as fixed inputs, which is not the semantics core.md §3 item 10 describes, and then states that the actual behavior is a Van Gelder alternating fixpoint with self-cyclic and subset-minimal ancestor filtering and source-SCC symmetric conflict locking, identified by kernel symbols (`defObstructed`, `mayPass`, `computeSourceSCCs`). The same document grounds other results in kernel internals (`#stageArchive`, `BoundarySystem.clone()`, `runClosure`, and `kind === "contingent"` for M1(ii)–(iii)). A second implementation written from core.md alone therefore cannot be checked against the reference kernel. MT-1 further records that cross-conflict mutual bridges between two distinct symmetric sources lie beyond single-source SCC isolation, while its audit table marks G-1, G-7 and G-15 `Resolved` and MT-1 carries `Consensus`. Affects core.md §3 items 8 and 10, MT-1, MT-2, MT-7, and G-1, G-7, G-15. | **Decided (Norman, 2026-11-25).** Define `Live` and `Collision` in core.md as the well-founded semantics (Van Gelder, Ross and Schlipf, 1991) of an explicit evaluation program `Π(Σ)`: rule schemas over atoms for ground entries, collisions, obstruction and authority, with negation only through obstruction, and with `B' ⊑ B` ranging over the boundaries declared in `Σ`. Transmission requires an entry that is true in the well-founded model (`Live`); `authority` is `Quarantined` when it is false and `Undetermined` when it is undefined; `Collision` is reported when the collision atom is true or undefined, so symmetric conflicts are recorded on both sides and transmit on neither. MT-1 is restated for `Π(Σ)`. A clean-room oracle written from core.md alone is compared with the kernel by differential fuzzing; the kernel either drops its SCC heuristics or is shown equivalent on that comparison, and every test whose expectation changes is decided by the maintainer. Kernel symbols leave the normative text for the reference-kernel map in README. **Refined (Norman, 2026-11-26, adopting the recommended options after review against the charter).** (G1) Positive conclusions, and exclusions inferred from positive evidence (incompatibility, `imposs-excl`), fire only from `Live` premises; the exclusion of a compound fires from the exclusion records of its components, while its context premises (the antecedent of a counterexample, domain membership `±δ`, cover cells) must be `Live`; every conclusion is `Live` only when all its premises are `Live` and its slot is unobstructed. (G2) `-∃` follows G1: for each handle, `Live -δ` or an exclusion record of the body, on a domain whose closure is witnessed ([audit-universal-existential-import](design-review.md#audit-universal-existential-import)). (G3) `Π(Σ)` is stated over facts `(B, ±, A)`, not provenance entries: a fact is `Live` when some rule instance with `Live` premises yields it and its slot is unobstructed, and provenance DAGs are witnesses of true atoms, not part of the semantics. (G4) A record counts as present when its atom is true or undefined, for local status and `Collision` alike; the authority axis carries the uncertainty, so a symmetric conflict reads `Collision` with `Undetermined` authority on both sides. (G5) The atom universe is finite: the tracked and queried items closed under sub-items, quantifier instances (body and `δ`) over `Dom(D)`, and congruence rewrites, with `~` applied only to tracked items. (G6) The kernel's iteration and cover-size bounds are not semantics: where they would truncate, the kernel reports non-convergence instead of returning a partial result. **Revised (Norman, 2026-11-26) after the differential comparison with the clean-room oracle of item 14.** (G4b, replacing G4) A record is present only when its atom is true; `Collision` is reported when the collision atom is true or undefined, so a possible conflict stays visible while no status rests on a merely possible record. Of the 21 readings of item 14 recorded by the oracle, A3 (a polarity flip nested in an item or a quantifier instance belongs to the universe), A6 (congruence rewrites one occurrence at a time, as item 6 states) and A13 (vacuous grounding requires `D ≠ ⊥_B`) were amended, and the rest were ratified as recorded. Across 1,500 random states, kernel and oracle diverged only where a conflict's resolution is undetermined under the well-founded semantics, which the SCC heuristics resolve skeptically. **Rulings (Norman, 2026-11-26) on the kernel alignment.** Tracked items include every item named by a transition in the history of `Σ`, retracted ones included, so M2's non-erasure stays observable; `⊥` is always tracked; a boundary with several parents defaults to the handles common to all of them; the kernel's new values for `(B, ⊥)` under a self-refuting pair of observations, for the multi-hop Scoped Cut scenario and for the matching MT-1 fuzz cases are accepted, and the fuzz invariant follows G4b. **Process (Norman, 2026-11-26).** A reading of the specification made by an implementation or an oracle becomes part of the specification only when it is written into `spec/`; it is never ratified by reference to a file under `test/` or `src/`. *Permits*: a second implementation that can be checked against the specification, and uniform treatment of every conflict shape, including cross-conflict bridges. *Excludes*: semantics defined by an algorithm's internal heuristics. *Rejected*: transcribing the current heuristics (self-contained on paper, but ad hoc, with the known bridge case left open and a novel construction to prove); stable-model semantics (a state may have no stable model or several, and skeptical reasoning is coNP-hard; the well-founded model is contained in every stable model, so the semantics can be strengthened later). **Reopen if:** the differential comparison finds a ratified worked example whose intended outcome the well-founded semantics cannot produce, or evaluating `Π(Σ)` becomes infeasible on the fuzzing workloads. | done: [README metatheory-to-kernel map](../README.md#metatheory-to-kernel-map); core.md §5 item 14 (commit "spec: define the evaluation program Π(Σ) and restate MT-1", commit "feat: evaluate Π(Σ) by its well-founded model in the reference kernel") |
| `audit-universal-existential-import` | **The kernel ties both quantifiers to a non-empty domain, giving universals existential import, while the `UL-Classical` evaluator uses classical vacuous truth.** `core.md` §3 item 12 grounds `+∀(x : D ⊓ [δ]) A(x)` generically only "with at least one admissible `+δ(x)` witness", and the kernel's `forall-generic` rule in [`src/engine.ts`](../src/engine.ts) also requires a non-empty `Dom(D)`. A universal over an empty domain, or over a constraint no handle satisfies, therefore never becomes `Grounded`, and since `-∀` needs a concrete counterexample it stays `Open`. This is the existential import of Aristotelian logic, an inherited default that neither core.md nor [glossary.md](glossary.md) flags under the Anti-Inertia Audit of [AGENTS.md](../AGENTS.md) §2. Dually, the kernel's `exists-excl` rule also requires a non-empty `Dom(D)`, so an existential over an empty domain stays `Open` although the `-∃` clause of item 12 holds vacuously there; this is a kernel deviation from item 12, and when `Dom(D)` is non-empty but no handle satisfies `δ` the kernel does derive `-∃`. The `UL-Classical` evaluator in [`src/specializations.ts`](../src/specializations.ts) gives classical values instead: vacuous truth (`+`) for the universals and `-` for the existentials. Applying the quantifier closure (C7) of core.md §4 item 13 to an empty `D_δ` would contradict item 12 for universals, so v0.3.0 excludes that case through (C8); for existentials (C7) follows item 12, so MT-9 is unaffected. The maintainer must decide whether existential import for universals is intended, and then record it as a deliberate departure, or whether generic grounding should admit vacuous truth; either way the kernel's existential rule should follow item 12. Executable reproduction: R4 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-26).** Exhaustiveness of a quantifier domain is witnessed, never assumed, as for covers and meets. A new `C_B` constraint `CloseDomain(D)`, registered by an inquiry transition and removable by `Withdraw`, records that the handles of `Dom(D)` at registration exhaust `D`. Enumerative generic grounding fires only on a closed domain: `+∀(x : D) A(x)` once every handle of `Dom(D)` carries `Live -δ` or else `Live +δ` with `Live +A`, and `-∃(x : D) A(x)` once every handle carries `Live -δ` or an exclusion record of `A`; the closure is a provenance leaf of both, so withdrawing it, or retracting any `-δ` exclusion, reopens them. With `D_δ := {w ∈ Dom(D) : Live +δ(w)}`, an empty `D_δ` yields vacuous truth grounded by the `-δ` exclusions and the closure, and an empty `Dom(D)` on a non-empty `D ≠ ⊥_B` yields vacuous truth grounded by the closure alone. On an unclosed domain, enumeration never grounds `+∀` or `-∃`; `+∀` then comes only from observation, schematic `∀I` or covers. `-∀` and `+∃` stay open-world: one witness suffices, with no closure. Three boundary rules apply. (1) A closure anchors the handle set it witnessed and becomes invalid, with a revision obligation, if `Dom(D)` changes, as covers do under [audit-cover-non-vacuity-drift](design-review.md#audit-cover-non-vacuity-drift). (2) Closure is a property of the quantifier domain `D`, not of the evaluation boundary, and does not pass to sub-boundaries `D' ⊑ D`, while a `+∀` ground still inherits downward across evaluation boundaries. (3) `UL-Classical` (C3) requires a witnessed closure and `Dom(D) ≠ ∅`, which `src/specializations.ts` checks together with `Dom(D) ⊆ Dom(B*)`; (C8) is withdrawn, MT-9 uses `min ∅ = 1` and `max ∅ = 0`, and MT-9 returns to `Tested` until the maintainer reviews the revised statement. The boundary system also enforces domain monotonicity, `Dom(D') ⊆ Dom(D)` whenever `D' ⊑ D` (core.md §2 item 6), which the eigenvariable typing of `∀E` (`eigenDom ⊑ D`) already presupposes: without it, a closed empty `D` with a handled sub-boundary would let `∀E` derive `+⊥` through a `∀I` box and violate MT-3. core.md §3 item 12 drops "with at least one admissible `+δ(x)` witness"; the kernel's `forall-generic` drops its admissible-witness requirement, and both enumerative rules require the closure and accept an empty `Dom(D)`. Impact measured at `6c490ea`: 2 of 40 tests rely on enumerative quantifier grounding and need a closure; no fixture violates monotonicity, and one fuzz negative test needs its error-check order adjusted. *Permits*: vacuous and non-vacuous universals and existential exclusions alike, backed by a witnessed and revisable exhaustiveness claim; the strong-negation duality `+∀x A ⟺ -∃x ~A` on every domain; classical recovery without a quantifier closure extension. *Excludes*: enumeration over an unwitnessed handle registry, empty or not; existential import as an unexamined default; sub-boundaries that add individuals their parent lacks. *Rejected*: symmetric existential import in `UL-Core` with a vacuous-truth closure in `UL-Classical` (approved and replaced earlier on 2026-11-26: a demonstrably empty `D_δ` is evidence, so import withholds well-founded grounds and needs a compensating closure); evidence-based vacuous truth over the registry as found (treats every handle registry as complete); vacuous truth for an empty `D_δ` but `Open` for an empty `Dom(D)` (separates the cases by emptiness alone, although a non-empty registry is just as unwitnessed); a definition-time `closedDomain` flag (an exhaustiveness claim must be withdrawable); allowing sub-boundaries to add handles and invalidating closures instead of enforcing monotonicity (would also require changing the eigenvariable typing of `∀E`). **Reopen if:** a ratified model needs a finer regime that introduces individuals its parent lacks, a ratified worked example relies on subalternation in `UL-Core`, or a closure-grounded vacuous result supports an immunization that M1 does not catch. | done: [`core.md`](../spec/core.md#2-boundary-algebra--inquiry-state-dynamics) §2 items 6 and 7 (domain monotonicity, `CloseDomain`, `Withdraw`), §3 item 12, §4 item 13 (C3), §5 item 14; [`metatheory.md`](../spec/metatheory.md) MT-9 (commit "spec: specify domain closure and the kernel-alignment rulings", commit "feat: evaluate Π(Σ) by its well-founded model in the reference kernel", commit "feat: enforce domain monotonicity and refuse truncated cover closures", commit "feat: require closed non-empty quantifier domains for UL-Classical (C3)", commit "feat: re-validate covers and withdraw constraints from C_B") |
| `audit-unverified-cover-authority` | **An unverified cover still witnesses, so `No-Gluts` depends on the query set.** `core.md` §2 item 5 lets an unverified cover witness cover-witnessed disjunction and Cover-Gluing. Reproduction: `C1, C2 ⊑ B` declared disjoint, `WitnessCover({C1, C2} ▷ B)`, and `B3 ⊑ B` of unknown overlap with both cells; `Observe⁺(C1, P)`, `Observe⁺(C2, Q)`, `Observe⁻(B3, P)`, `Observe⁻(B3, Q)`. With `Q = ∅` nothing collides (two `OverlapUnknown` obligations and the cover's obligation are recorded); querying `P ∨ Q` grounds it on `B` through the unverified cover, the record inherits to `B3`, and `(B3, P ∨ Q)` collides with no atom colliding anywhere, the pattern of R2. `isCollisionFree`, and with it the `No-Gluts` checks of the specializations and of the proof checker, then varies with `Q`. A valid cover cannot do this: every sub-boundary is known to overlap a cell, so the conflict already collides on atoms. In tension with `CHARTER.md` Principles 3 and 4. Revisits the unverified case of [`audit-cover-non-vacuity-drift`](design-review.md#audit-cover-non-vacuity-drift). Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 2). Executable reproduction: R5 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** An unverified cover witnesses nothing until its unsettled sub-boundaries are settled: it supplies no cover-witnessed disjunction, `∨E` or Cover-Gluing instance and seeds no derived cover, and it keeps its revision obligation. The witnessed covers of `Σ` are then the valid registered covers closed under Axioms 2–4, all of them valid, and the "valid, not merely unverified" of (C3) reduces to "witnessed". A property test checks query conservativity: adding queries changes neither the statuses of the slots of `U(Σ, ∅)` nor `No-Gluts`. *Permits*: covers that ground only once their exhaustiveness is settled against the registry. *Excludes*: collisions that appear only when a compound is queried (R5). *Rejected*: keeping unverified covers authoritative (R5); letting them yield records without authority (opposite records would still collide, so `No-Gluts` would still vary with the query set). Cost: a sub-boundary defined without settling its overlaps with the cells suspends a cover until those overlaps are declared or registered. **Reopen if:** query conservativity fails with valid covers alone, or suspending covers blocks a ratified worked example. | decided |
| `audit-eager-ambiguous-meet` | **The kernel throws on ambiguous meets that nothing needs.** `core.md` §5 item 14 (Role) reports an error where "a meet the program needs is ambiguous", and the oracle reads that lazily (readings A31 and A35 in `test/oracle/AMBIGUITIES.md`). `src/engine.ts` calls `meetStatus` for every pair of boundaries while collecting `OverlapUnknown` obligations, so `evaluate()` throws whenever any pair is ambiguous, even with no implication tracked and no opposite records; `#assessCover` in `src/boundary.ts` computes the meet of every cell with a sub-boundary before checking whether one cell is already known to overlap it, so the validity check of a cover whose sub-boundaries all lie below cells throws. The differential suite builds no ambiguous topology, so kernel and oracle are not compared there. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 3). Executable reproduction: R6 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** The kernel computes a meet only where item 14 needs it: for Scoped Cut once `U(Σ, Q)` holds an implication, for `OverlapUnknown` only between boundaries holding opposite present records, for a cover's validity only for a sub-boundary known to overlap no cell when no other sub-boundary refutes the cover, and for a base change only when it is computed; elsewhere an ambiguous pair is not an error. Item 14's Role states this (the oracle's readings A31 and A35), and the differential suite adds ambiguous topologies. *Permits*: evaluating states that hold an ambiguous pair nothing depends on. *Excludes*: errors from meets no rule consults (R6). *Rejected*: an error for any ambiguous pair of `𝔅(Σ)` (simpler, but one unrelated ambiguity would make every evaluation fail, against item 14's own wording). **Refined (Norman, 2026-11-28).** Scoped Cut needs an ambiguous meet only for an instance over the pair whose `Live` premises are true in the least model of the program read with every `obs` atom false and with the instances over ambiguous pairs left out; otherwise the instance can never fire, and its conclusion boundary decides nothing. This replaces "once `U(Σ, Q)` holds an implication" (the oracle's first reading A31), under which an unrelated conditional was enough to fail every evaluation, unlike the rules for `OverlapUnknown` and covers. *Rejected*: keeping the coarser rule (simpler to state, but it refuses states whose result does not depend on the meet). **Reopen if:** a result of `Π(Σ)` depends on an ambiguous meet that this rule does not consult. | done: [`core.md` §5](../spec/core.md#5-evaluation-program) item 14, Role (commit "feat: compute meets where needed, keep identifiers unique, complete checks", commit "spec: state identifiers, refinement requests, freshness and needed meets") |
| `audit-theorem-dependency-gaps` | **Recorded theorems keep authority their derivations no longer have.** The `Theorem` row of `core.md` §5 item 14 makes a recorded theorem depend on the base observations it names and the grounds it requires. (a) `or-cover-intro` and `cover-glue` in `src/deduction.ts` record no dependency on the cover, so after `Withdraw` of the cover, or its invalidation, the theorem stays `Live`. (b) `live-ground` pins the base leaves of the first `Live` entry it finds, so the same facts observed in two orders react differently to `Retract` of one observation, against the Exchange of co-present `Live` grounds (§3 item 11). (c) A `UL-Intuitionistic` theorem admitted under `No-Gluts`, such as `(A ∧ (A → ⊥)) → C` by `ex-falso-bottom`, names nothing, so once later monotone observations break `No-Gluts` it turns an excluded `C` into `Collision`, the explosion §3 item 10 excludes from `UL-Core`. Affects `metatheory.md` MT-6 and MT-8b. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 4). Executable reproduction: R7 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** (a) A recorded theorem names the constraints its derivation uses, covers included, and the `Theorem` row fires only while each is in `C_B` and, for a cover, witnessed, so withdrawing or invalidating one disables the theorem. (b) `live-ground` makes the cited slot a required `Live` ground and names no base observation unless the proof names one explicitly, so a theorem's authority does not depend on observation order. (c) A derivation that uses a rule outside `UL-Core` (`ex-falso-bottom`) can be verified but is not admitted into `Σ`. *Permits*: recorded theorems that lose authority exactly with their dependencies. *Excludes*: theorems that survive `Withdraw` or invalidation of their cover, authority that depends on observation order, and explosion imported from `UL-Intuitionistic` (R7). *Rejected*: gating mode theorems on `No-Gluts` inside `Π(Σ)` (needs negation over collisions beyond `obs`, which item 14 forbids); pinning a chosen observation in (b) (keeps the order dependence). **Reopen if:** a recorded `UL-Core` theorem stays `Live` after a dependency it names is retracted, withdrawn or invalidated, or a needed `UL-Intuitionistic` result cannot be used without admitting it into `Σ`. | decided |
| `audit-mt8b-statement` | **MT-8b is circular or false as worded.** `metatheory.md` MT-8b states that every accepted derivation, "once recorded into `Σ`", yields only grounds that evaluation of `Σ` licenses where its dependencies are `Live`. Read after recording, the `Theorem` row of `core.md` §5 item 14 licenses the recorded ground by construction, so the statement says nothing; read before recording, `Π(Σ)` has no `→I` and no schematic `∀I`, so `B ⊩⁺ (P → P)`, which the checker accepts on an empty `Σ`, is `Open` there, and the statement is false. MT-8b needs a statement with content, for instance that recording a verified derivation preserves MT-3, MT-4 and MT-6 and loses authority with any of its dependencies (see `audit-theorem-dependency-gaps`). Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 4). | **Decided (Norman, 2026-11-28).** MT-8b is restated as dependency soundness: a recorded `UL-Core` theorem is `Live` only while every base observation, constraint and ground it names is in force and `Live`, and its authority is invariant under the order of observations. It stays `[Exploratory]` until a property test binds it, and then becomes `[Tested]`. *Permits*: a claim that tests can refute. *Excludes*: the circular and the false readings of the present wording. *Rejected*: a broader statement bundling MT-3, MT-4, MT-6 and MT-9 across all extensions (too wide to test or prove now); dropping MT-8b (leaves the bridge between the proof checker and evaluation without any claim). **Reopen if:** a property test refutes the restated claim, or a needed property of recorded theorems falls outside it. | decided |
| `audit-deduction-freshness-and-congruence` | **The proof checker's freshness and congruence differ from the evaluation program.** `forall-intro` and `exists-elim` check eigenvariable freshness against `mentionedHandles()`, which omits handles named only by retracted observations, withdrawn constraints, refinements and other tracked items, although `core.md` §5 item 14 keeps those items tracked. `equiv-subst` rewrites every occurrence of a handle at once and does not check that the new handle belongs to a domain of `𝔅(Σ)`, while §2 item 6 and item 14 rewrite one position at a time over registered handles (oracle readings A5 and A6). Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 4). Executable reproduction: R8 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** Eigenvariable freshness in `forall-intro` and `exists-elim` is checked against every handle that `Σ` tracks: the items of retracted observations and withdrawn constraints, refinements, and registered domains. `equiv-subst` rewrites one occurrence at a time, to a handle of a domain in `𝔅(Σ)`, as §2 item 6 and item 14 do. *Permits*: a proof checker and an evaluation program that agree on handles and congruence. *Excludes*: eigenvariables that clash with tracked handles (R8), and rewrites the evaluation program cannot follow. *Rejected*: freshness against current observations only (a retracted handle could reappear as a fresh eigenvariable while it stays tracked). **Reopen if:** a ratified derivation needs a multi-position rewrite that one-position steps cannot reach. | done: [`core.md` §3](../spec/core.md#3-dual-polarity-semantics-provenance--derivation-calculus) item 12, and §2 item 6 (commit "feat: compute meets where needed, keep identifiers unique, complete checks", commit "spec: state identifiers, refinement requests, freshness and needed meets") |
| `audit-classical-check-completeness` | **The `UL-Classical` check accepts states that violate (C3), (C4) or (C6).** `evaluateClassicalSpecialization` in `src/specializations.ts` evaluates only the queried items, so a tracked compound such as `+((P → Q) → P)` with `-P` and `-Q` is never compared with `v(P → Q) = +`; it ignores registered incompatibilities and structural collapses, so both sides of `(P → Q) ⊥ (Q → P)` can receive `+`; `evalOnAtomicCell` short-circuits `∧`, `∨` and the quantifier loops, so a conflicting ground on a skipped sub-item is never checked; and handles named outside quantifiers are not checked against `Dom(B*)`, which (C3) asks for. Affects the kernel check behind MT-9, not its proof, and MT-9b. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 5). Executable reproduction: R9 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** `evaluateClassicalSpecialization` evaluates every level-0 tracked item and every query on every atomic cell without short-circuiting, checks each registered incompatibility (its sides are never both `+` on a cell below its boundary) and structural collapse (its item is `-` there), and checks every handle the items name against `Dom(B*)`, refusing unbound variables. *Permits*: a `UL-Classical` valuation that agrees with every ground and constraint of `Σ`. *Excludes*: accepting states that violate (C3), (C4) or (C6) (R9). *Rejected*: documenting the check as partial (the kernel check behind MT-9 could then not reject the states it is meant to reject). **Reopen if:** the complete check refuses a state that (C1)–(C7) admit. | done: [`core.md` §4](../spec/core.md#4-boundary-specialization-theorems) item 13, (C3), (C4) and (C6) (commit "feat: compute meets where needed, keep identifiers unique, complete checks", commit "spec: state identifiers, refinement requests, freshness and needed meets") |
| `audit-m1-indirect-overblocking` | **M1(i)'s indirect-reference graph refuses independent criteria.** `core.md` §2 item 7 links, as one undirected graph, every pair of relations that occur together in an incompatibility, a structural collapse, or a conditional `Live` on any boundary. Two background conditionals with a shared consequence (`Lake(x) → Alive(x)`, `White(x) → Alive(x)`) then connect `Lake` to `White` and refuse a refinement by `Lake` as `M1-circular`, although `Lake` neither aliases nor depends on `White`; conditionals on unrelated boundaries count as well. `refineBoundary` also admits a `targetRelation` that does not occur in the universal, and a refinement that excises no handle. Revisits the M1(i) part of [`audit-m1-criterion-decoupling`](design-review.md#audit-m1-criterion-decoupling). Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 6). Executable reproduction: R10 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** M1(i) indirect reference becomes directed, boundary-scoped inference reachability: `δ` refers to the target relation indirectly when `+A` is reachable from `+δ` along the edges item 14 fires, from the antecedent to the consequent of a conditional `Live` on `B` or a boundary above it, and from one side of an incompatibility registered on `B` or above to the exclusion of the other. Shared consequences and shared exclusions no longer link two relations. `refineBoundary` also refuses a `targetRelation` that does not occur in the universal, and a refinement that excises no handle. *Permits*: criteria that share background consequences with the target. *Excludes*: criteria that entail the target, directly or through registered links, which is the immunization M1 blocks; empty and mistargeted refinements (R10). *Rejected*: the undirected global graph (refuses independent criteria); dropping the indirect check (lets aliases of the target through). **Reopen if:** a criterion that aliases the target passes, or the ratified refinements of worked-examples.md §1 and §2 are refused. | decided |
| `audit-identifier-reuse` | **Reusing an observation or theorem identifier silently replaces the earlier entry.** `#addBaseObservation` and `recordTheorem` in `src/engine.ts` overwrite an entry with the same identifier, and `retract` frees an identifier for reuse, unlike constraint identifiers, which are never reused. Under `monotoneOnly`, where `Retract` is refused, observing again under an earlier identifier erases the earlier observation, bypassing that refusal and the non-erasure of M2. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 7). Executable reproduction: R11 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** Base observation and theorem identifiers are unique for the life of an inquiry, as constraint identifiers are: reuse is refused, also after `Retract`. *Permits*: identifiers that each name one transition. *Excludes*: erasing an observation under `monotoneOnly` by reusing its identifier, and silently replacing a theorem (R11). *Rejected*: allowing reuse after `Retract` only (the history would then name two observations by one identifier). **Reopen if:** a ratified workflow needs to replace an observation in place. | done: [`core.md` §2](../spec/core.md#2-boundary-algebra--inquiry-state-dynamics) item 7 (commit "feat: compute meets where needed, keep identifiers unique, complete checks", commit "spec: state identifiers, refinement requests, freshness and needed meets") |
| `audit-free-handle-policy` | **Observations may name handles outside the boundary's domain.** `observePositive` and `observeNegative` make `HandleAuth` optional and do not check that the handles of the item belong to `Dom(B)`, so unregistered handles enter `U(Σ, Q)`, the proof checker rewrites them by `equiv-subst`, and the `UL-Classical` check accepts them (R9, part d). `core.md` §2 item 6 does not say whether `Observe±(B, A)` is many-sorted, with the handles of `A` in `Dom(B)` and authenticated under `I_B`, or follows a free logic. A ruling should measure first how many fixtures name handles outside their boundary's domain. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 7). | **Decided (Norman, 2026-11-28).** `Observe±` is many-sorted: every handle of an observed item belongs to `Dom(B)` (§2 item 6), and `HandleAuth`, when given, authenticates it under `I_B`. Before the kernel enforces this, the number of fixtures that name handles outside their boundary's domain is measured, and the ruling is reviewed if that impact is large. *Permits*: handles tied to the boundaries that admit them, consistent with (C3). *Excludes*: unregistered handles entering `U(Σ, Q)`, and proof-checker rewrites to them. *Rejected*: a free logic (needs existence predicates throughout the rules and the quantifier clauses). **Reopen if:** a ratified example needs to observe an individual before any boundary admits it. | decided |
| `audit-boundary-mutation-staging` | **Boundary edits bypass the inquiry stages.** `defineBoundary`, `declareDisjoint`, `defineMeet` and `registerCover` change the boundary system without a transition of `core.md` §2 item 7, so `evaluate()`, which reads the live boundary system, and `evaluateAtStage` at the current stage, which reads the snapshot taken at the last transition, disagree; and a cover registered directly cannot be withdrawn through `Withdraw`. Item 14's `𝔅(Σ)`, "the non-empty boundaries declared in `Σ`", leaves open whether boundary declarations are transitions. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 8). Executable reproduction: R12 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** Declaring boundaries, disjointness and meets is an inquiry transition. The kernel stages every change of the boundary system: it detects a new boundary-system version and records a `Declare` stage before it evaluates, and it adopts a cover registered directly as a constraint that `Withdraw` can name. *Permits*: `evaluate` and `evaluateAtStage` at the current stage to agree, and every cover to be withdrawable. *Excludes*: R12. *Rejected*: forbidding direct boundary edits once an engine exists (breaks the boundary-system-first API that most fixtures use); documenting the split (two answers for one stage). **Reopen if:** staging records a stage that no change of `Σ` caused, or misses one. | decided |
| `audit-reflection-authority-flattening` | **A stage-indexed reflection reads an `Undetermined` record as excluded.** The kernel gives a reflection the value `+` when its target record is `Live` at the frozen stage and `-` otherwise, so an `Undetermined` authority becomes `Excluded`: a definite answer where `core.md` §5 item 14 reports an undetermined one, against `CHARTER.md` Principle 4. §1 item 3 does not say which value a reflection on an `Undetermined` record takes. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 8). Executable reproduction: R13 under [Audit Reproductions](design-review.md#audit-reproductions). | **Decided (Norman, 2026-11-28).** A stage-indexed reflection on a record takes `+` when the record is `Live` at its stage, `-` when it is `Quarantined` or absent, and no value when its authority is `Undetermined`, so the reflection stays `Open`. *Permits*: reflections that report no more than item 14 settles. *Excludes*: definite answers about undetermined authority (R13). *Rejected*: `-` for `Undetermined` (the current behavior); both values (would manufacture a collision). **Reopen if:** a ratified use of reflection needs a definite value for an undetermined record. | decided |
| `audit-unexecuted-syntax` | **Stage-less reflection and recursive references have syntax but no evaluation.** `core.md` §1 items 2 and 3 admit stage-less `Refl_k(J)` and `ref(name)`. The kernel leaves stage-less reflection permanently `Open`, the proof checker refuses it, and `ref` is checked statically by `checkRecursiveDefinitionSystem` but unfolded nowhere. The specification should say which of them belong only to a formal layer and which execute, or give them evaluation rules. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 8). | **Decided (Norman, 2026-11-28).** Stage-less `Refl_k(J)` and `ref(name)` belong to the formal layer only: they are checked for well-formedness and stratification (the Curry firewall of §1 item 3) and receive no value in `UL-Core`, so they stay `Open`. §1 items 2 and 3 and the README say so. *Permits*: the syntax to keep its role in the Curry firewall without unused semantics. *Excludes*: reading them as evaluated items. *Rejected*: specifying finite unfolding or stage-less evaluation now (no ratified use, and it reopens self-reference risks). **Reopen if:** a ratified example needs a stage-less reflection or a recursive reference to carry a value. | decided |
| `audit-oracle-readings-promotion` | **Load-bearing oracle readings exist only under `test/`.** The clean-room oracle records its readings A22–A39 of `core.md` §2 items 4, 5 and 7 and §5 item 14 in `test/oracle/AMBIGUITIES.md`, all `[Exploratory]`, and the kernel agrees with them on the differential suite. Under the process ruling of [`audit-spec-kernel-coupling`](design-review.md#audit-spec-kernel-coupling), a reading becomes specification only when written into `spec/`. Each reading needs a ruling, and the load-bearing ones need to be written into §2 and item 14 before v0.3.0. Raised by an external review of `dfa0fb9` (2026-11-27, pre-freeze checklist item 9). | **Decided (Norman, 2026-11-28).** Readings A22–A39 are ratified. Those that carry semantics are written into the specification: A28 and A29 (the shape and trigger of `OverlapUnknown`) into item 14; A31 and A35 (where an ambiguous meet is an error) into item 14 together with the kernel fix of `audit-eager-ambiguous-meet`; A32, A33 and A34 (a blocked base change owes nothing, the range of `B'`, the content of a cover obligation) into item 5; A37 and A39 are already there. A22–A27, A30, A36 and A38 describe the oracle's representation or follow from the text, and need no new text; A25's remark that domain monotonicity is not enforced is out of date (enforced since `2db33cd`) and is dropped. Under `audit-unverified-cover-authority`, the closure of A36 starts from valid covers only. *Permits*: a specification that holds every reading a result of `Π(Σ)` turns on. *Excludes*: semantics that live only under `test/`. *Rejected*: writing every reading into the specification (would put one implementation's representation choices into it). **Reopen if:** a reading kept out of the specification turns out to decide a result of `Π(Σ)`. | done: [`core.md` §2](../spec/core.md#2-boundary-algebra--inquiry-state-dynamics) item 5 and §5 item 14 (commit "spec: write ratified readings into items 5 and 14 and flag pending audits", commit "spec: state identifiers, refinement requests, freshness and needed meets") |
| `audit-terminology-drift` | **Descriptive text lags the ratified semantics.** In `docs/glossary.md`, `Inference Quarantine` still cites source-SCC conflict locking instead of `Π(Σ)` and the two status axes, `Pure Cancellation (Retract)` omits `Withdraw`, `Boundary-Scoped Quantifiers` omits `CloseDomain`, and `Structural Anti-Immunization (M1)` lists M1(i)–(iii) without M1(iv) (external review, pre-freeze checklist item 10). In `core.md`, the Scoped Cut of §3 item 11 and the Meet Collision Corollary of item 9 still read the meet condition as `B₁ ⊓ B₂ ≠ ⊥_B`, where item 4 and item 14 now ask for a known overlap (found while checking the review). | **Decided (Norman, 2026-11-28).** Update the four glossary entries to the evaluation program `Π(Σ)` with the two status axes, `Withdraw`, `CloseDomain` and M1(iv), and make the meet conditions of §3 items 9 and 11 read "known to overlap", as items 4 and 14 do. *Permits*: descriptive text that agrees with the ratified items. *Excludes*: definitions that teach superseded mechanics. *Rejected*: deleting the glossary entries (they carry the terminology boundaries that AGENTS.md §2 item 3 asks to record). **Reopen if:** a descriptive passage again disagrees with a ratified item it describes. | done: [`core.md` §3](../spec/core.md#3-dual-polarity-semantics-provenance--derivation-calculus) items 9 and 11; [`glossary.md`](glossary.md) (commit "spec: write ratified readings into items 5 and 14 and flag pending audits", commit "docs: update four glossary entries to the ratified semantics") |

### Audit Reproductions

Each snippet reproduces the kernel behavior cited by an implementation entry above, at the commit that entry names (`785b74e` for R1–R3, `7fd4c6d` for R4, `2713cba` for R5–R13). Each is self-contained: save it as a `.ts` file in the repository root and run `node <file>.ts` with the Node version `npm test` uses (Node 22+ with type stripping). Every assertion records the current, defective behavior, so a snippet that starts failing means the behavior has changed.

#### R1: M1 accepts a criterion that the excised counterexample satisfies

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, forall } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("Swan", {
  nativeRelations: ["White", "Feathered"],
  handles: [
    { id: "swan_402", criterion: "I_Swan", kind: "contingent" },
    { id: "swan_101", criterion: "I_Swan", kind: "contingent" },
  ],
});
b.defineBoundary("Swan_Rest", { parents: ["Swan"], handleFilter: (h) => h.id !== "swan_402" });
const e = new InquiryEngine(b);
const rel = (name: string, handle: string) => atom(name, [{ role: "subject", handle }]);
const auth = (handle: string) => ({ handle, criterion: "I_Swan" });
e.observeNegative("Swan", rel("White", "swan_402"), "obs_black", auth("swan_402"));
e.observePositive("Swan", rel("Feathered", "swan_101"), "f101", auth("swan_101"));
e.observePositive("Swan", rel("Feathered", "swan_402"), "f402", auth("swan_402"));

const res = e.refineBoundary({
  fromBoundary: "Swan",
  toBoundary: "Swan_Rest",
  originalUniversal: forall("x", "Swan", rel("White", "x")),
  targetRelation: "White",
  criterionItem: rel("Feathered", "x"),
});
assert.equal(res.ok, true); // refinement admitted
const excised = rel("Feathered", "swan_402");
assert.equal(e.evaluate([excised]).isLive("Swan", "+", excised), true); // yet the excised handle satisfies δ
```

#### R2: A cover survives a sub-boundary disjoint from every cell; `statusOf` ignores obstruction

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, or } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("B");
b.defineBoundary("C1", { parents: ["B"] });
b.defineBoundary("C2", { parents: ["B"] });
b.declareDisjoint("C1", "C2");
const e = new InquiryEngine(b);
e.witnessCover("B", ["C1", "C2"]);
b.defineBoundary("B3", { parents: ["B"] });
b.declareDisjoint("B3", "C1");
b.declareDisjoint("B3", "C2");
assert.equal(b.isWitnessedCover("B", ["C1", "C2"]), true); // still accepted as exhaustive

const P = atom("P");
const Q = atom("Q");
const PQ = or(P, Q);
e.observePositive("C1", P, "p1");
e.observePositive("C2", Q, "q2");
let s = e.evaluate([PQ]);
assert.equal(s.statusOf("B3", PQ), "Grounded"); // disjunction grounded on B3 ...
assert.equal(s.statusOf("B3", P), "Open"); // ... with neither disjunct known there
assert.equal(s.statusOf("B3", Q), "Open");

e.observeNegative("B3", P, "np3");
e.observeNegative("B3", Q, "nq3");
s = e.evaluate([PQ]);
assert.equal(s.statusOf("B3", PQ), "Collision");
for (const bd of ["B", "C1", "C2", "B3"]) {
  assert.equal(s.isCollided(bd, P), false); // no disjunct collides anywhere
  assert.equal(s.isCollided(bd, Q), false);
}
assert.deepEqual(s.revisionObligations().map((r) => r.boundary), ["B3"]);

// audit-status-obstruction-mismatch
assert.equal(s.statusOf("B", PQ), "Grounded");
assert.equal(s.isObstructed("B", PQ), true);
assert.equal(s.isLive("B", "+", PQ), false);
```

#### R3: No registered common sub-boundary is read as disjointness; meet can be ambiguous

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("Lab");
b.defineBoundary("Field");
const e = new InquiryEngine(b);
e.observePositive("Lab", atom("P"), "lab");
e.observeNegative("Field", atom("P"), "field");
assert.equal(b.meet("Lab", "Field"), "⊥_B"); // never declared disjoint
assert.equal(e.evaluate().isCollisionFree(), true);

b.defineBoundary("LabField", { parents: ["Lab", "Field"] });
assert.equal(e.evaluate().isCollisionFree(), false); // the same evidence now collides

b.defineBoundary("LabField2", { parents: ["Lab", "Field"] });
assert.throws(() => b.meet("Lab", "Field"), /Ambiguous meet/); // ⊓ is not total
```

#### R4: Quantifiers over empty domains stay `Open` in `UL-Core` but take classical values in the `UL-Classical` evaluator

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { evaluateClassicalSpecialization } from "./src/specializations.ts";
import { atom, exists, forall, itemKey } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("B_star", {
  nativeRelations: ["P", "Q"],
  handles: [{ id: "a", criterion: "I_a", kind: "structural" }],
});
b.defineBoundary("Empty", { handles: [] });
const e = new InquiryEngine(b, { monotoneOnly: true });
const of = (rel: string, handle: string) => atom(rel, [{ role: "subject", handle }]);
const P = of("P", "a");
const Q = of("Q", "a");
e.observeNegative("B_star", P, "np"); // no handle satisfies δ := P(x)
e.observeNegative("B_star", Q, "nq");
const restricted = forall("x", "B_star", of("Q", "x"), of("P", "x")); // empty D_δ
const allEmpty = forall("x", "Empty", of("Q", "x")); // empty Dom(D)
const someEmpty = exists("x", "Empty", of("Q", "x")); // empty Dom(D)
const someRestricted = exists("x", "B_star", of("Q", "x"), of("P", "x")); // empty D_δ, non-empty Dom(D)
const items = [restricted, allEmpty, someEmpty, someRestricted];

const s = e.evaluate(items);
assert.equal(s.statusOf("B_star", restricted), "Open"); // no +∀ without a +δ witness
assert.equal(s.statusOf("B_star", allEmpty), "Open"); // no +∀ over an empty domain
assert.equal(s.statusOf("B_star", someEmpty), "Open"); // no -∃ over an empty domain either
assert.equal(s.statusOf("B_star", someRestricted), "Excluded"); // -∃ when Dom(D) is non-empty

const cl = evaluateClassicalSpecialization(e, "B_star", [P, Q], items);
assert.equal(cl.ok, true);
if (cl.ok) {
  const pol = (item: (typeof items)[number]) => cl.results.get(itemKey(item))?.polarity;
  assert.equal(pol(restricted), "+"); // classical vacuous truth
  assert.equal(pol(allEmpty), "+");
  assert.equal(pol(someEmpty), "-");
  assert.equal(pol(someRestricted), "-");
}
```

#### R5: An unverified cover makes `No-Gluts` depend on the query set

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, or } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("B");
b.defineBoundary("C1", { parents: ["B"] });
b.defineBoundary("C2", { parents: ["B"] });
b.declareDisjoint("C1", "C2");
b.defineBoundary("B3", { parents: ["B"] }); // its overlap with C1 and with C2 is unknown
const e = new InquiryEngine(b);
e.witnessCover("B", ["C1", "C2"]);
const P = atom("P");
const Q = atom("Q");
e.observePositive("C1", P, "p1");
e.observePositive("C2", Q, "q2");
e.observeNegative("B3", P, "np3");
e.observeNegative("B3", Q, "nq3");

const plain = e.evaluate();
assert.equal(plain.coverObligations()[0]?.validity, "unverified");
assert.equal(plain.isCollisionFree(), true); // Q = ∅: no collision
const queried = e.evaluate([or(P, Q)]);
assert.equal(queried.localStatus("B", or(P, Q)), "Grounded"); // through the unverified cover
assert.equal(queried.localStatus("B3", or(P, Q)), "Collision");
assert.equal(queried.isCollisionFree(), false); // querying P ∨ Q creates a collision
```

#### R6: Evaluation and cover validity throw on ambiguous meets that nothing needs

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom } from "./src/syntax.ts";

// Evaluation: Lab ⊓ Field is ambiguous, yet no implication is tracked and no opposite records exist.
const b = new BoundarySystem();
b.defineBoundary("Lab");
b.defineBoundary("Field");
b.defineBoundary("M1", { parents: ["Lab", "Field"] });
b.defineBoundary("M2", { parents: ["Lab", "Field"] });
const e = new InquiryEngine(b);
e.observePositive("Lab", atom("P"), "w");
assert.throws(() => e.evaluate(), /Ambiguous meet for "Lab" and "Field"/);

// Cover validity: every sub-boundary of B lies below a cell, so no meet decides anything, yet the
// check computes the ambiguous meet of C1 and C2.
const c = new BoundarySystem();
c.defineBoundary("B");
c.defineBoundary("C1", { parents: ["B"] });
c.defineBoundary("C2", { parents: ["B"] });
c.defineBoundary("S", { parents: ["C1"] });
c.defineBoundary("T1", { parents: ["S", "C2"] });
c.defineBoundary("T2", { parents: ["S", "C2"] });
const id = c.registerCover("B", ["C1", "C2"]);
assert.throws(() => c.coverValidity(id), /Ambiguous meet/);
```

#### R7: Recorded theorems outlive their cover, depend on observation order, and explode after `No-Gluts` breaks

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { admitVerifiedDerivation } from "./src/deduction.ts";
import { InquiryEngine } from "./src/engine.ts";
import { and, atom, bottom, implies, or } from "./src/syntax.ts";

const P = atom("P");
const Q = atom("Q");

// (a) A theorem proved through a cover keeps its authority after Withdraw of the cover.
{
  const b = new BoundarySystem();
  b.defineBoundary("B");
  b.defineBoundary("C1", { parents: ["B"] });
  b.defineBoundary("C2", { parents: ["B"] });
  b.declareDisjoint("C1", "C2");
  const e = new InquiryEngine(b);
  const cover = e.witnessCover("B", ["C1", "C2"]);
  e.observePositive("C1", P, "p1");
  e.observePositive("C2", Q, "q2");
  const res = admitVerifiedDerivation(e, {
    kind: "or-cover-intro",
    boundary: "B",
    left: P,
    right: Q,
    cellProofs: [
      { cell: "C1", proof: { kind: "live-ground", boundary: "C1", polarity: "+", item: P } },
      { cell: "C2", proof: { kind: "live-ground", boundary: "C2", polarity: "+", item: Q } },
    ],
  }, "thm");
  assert.equal(res.ok, true);
  e.withdraw(cover);
  assert.equal(e.evaluate([or(P, Q)]).isLive("B", "+", or(P, Q)), true);
}

// (b) live-ground pins the first Live entry: the same facts in two orders react differently to Retract.
{
  const run = (order: readonly string[]): string => {
    const b = new BoundarySystem();
    b.defineBoundary("B");
    const e = new InquiryEngine(b);
    for (const id of order) {
      e.observePositive("B", P, id);
    }
    admitVerifiedDerivation(e, {
      kind: "implies-intro",
      boundary: "B",
      assumptionId: "h",
      antecedent: Q,
      body: { kind: "live-ground", boundary: "B", polarity: "+", item: P },
    }, "thm");
    e.retract("w1");
    return e.evaluate([implies(Q, P)]).localStatus("B", implies(Q, P));
  };
  assert.equal(run(["w1", "w2"]), "Open");
  assert.equal(run(["w2", "w1"]), "Grounded");
}

// (c) A UL-Intuitionistic ex-falso theorem names nothing, so after monotone growth breaks No-Gluts
// it turns an excluded C into Collision.
{
  const A = atom("A");
  const C = atom("C");
  const build = (withTheorem: boolean): string => {
    const b = new BoundarySystem();
    b.defineBoundary("B");
    const e = new InquiryEngine(b, { monotoneOnly: true });
    if (withTheorem) {
      const h = { kind: "assume", assumptionId: "h", boundary: "B" } as const;
      const res = admitVerifiedDerivation(e, {
        kind: "implies-intro",
        boundary: "B",
        assumptionId: "h",
        antecedent: and(A, implies(A, bottom())),
        body: {
          kind: "ex-falso-bottom",
          target: C,
          bottomProof: {
            kind: "implies-elim",
            premise: { kind: "and-elim", pair: h, side: "left" },
            conditional: { kind: "and-elim", pair: h, side: "right" },
          },
        },
      }, "thm", "UL-Intuitionistic");
      assert.equal(res.ok, true);
    }
    e.observePositive("B", A, "wa");
    e.observePositive("B", implies(A, bottom()), "wna");
    e.observeNegative("B", C, "wnc");
    return e.evaluate([C]).localStatus("B", C);
  };
  assert.equal(build(false), "Excluded");
  assert.equal(build(true), "Collision");
}
```

#### R8: Eigenvariable freshness ignores handles named only by a retracted observation

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { admitVerifiedDerivation } from "./src/deduction.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, implies, itemKey } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("D", { nativeRelations: ["R"], handles: [{ id: "t1", criterion: "I", kind: "structural" }] });
const e = new InquiryEngine(b);
const r = (x: string) => atom("R", [{ role: "arg", handle: x }]);
e.observePositive("D", r("ghost"), "wg");
e.retract("wg"); // R(ghost) stays tracked (core.md §5 item 14)
assert.ok(e.evaluate().universe().map(itemKey).includes(itemKey(r("ghost"))));
const res = admitVerifiedDerivation(e, {
  kind: "forall-intro",
  boundary: "D",
  variable: "x",
  domain: "D",
  eigenvar: "ghost", // not fresh with respect to Σ's tracked items
  templateBody: implies(r("x"), r("x")),
  body: {
    kind: "implies-intro",
    boundary: "D",
    assumptionId: "h",
    antecedent: r("ghost"),
    body: { kind: "assume", assumptionId: "h", boundary: "D" },
  },
}, "thm");
assert.equal(res.ok, true);
```

#### R9: The `UL-Classical` check misses tracked compounds, constraints, short-circuited conflicts and foreign handles

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { evaluateClassicalSpecialization } from "./src/specializations.ts";
import { and, atom, implies, type Item } from "./src/syntax.ts";

const run = (setup: (e: InquiryEngine) => void, atoms: readonly Item[], queries: readonly Item[]): string[] | null => {
  const b = new BoundarySystem();
  b.defineBoundary("Bs", { nativeRelations: ["H"], handles: [{ id: "k", criterion: "I", kind: "structural" }] });
  const e = new InquiryEngine(b, { monotoneOnly: true });
  setup(e);
  const res = evaluateClassicalSpecialization(e, "Bs", atoms, queries);
  return res.ok ? [...res.results.values()].map((v) => v.polarity) : null;
};
const [P, Q, A, B, C] = ["P", "Q", "A", "B", "C"].map((n) => atom(n));

// (a) A tracked compound outside the queries: +((P → Q) → P) with -P and -Q, yet v(P → Q) = +.
assert.deepEqual(run((e) => {
  e.observeNegative("Bs", P, "np");
  e.observeNegative("Bs", Q, "nq");
  e.observePositive("Bs", implies(implies(P, Q), P), "w");
}, [P, Q], [implies(P, Q)]), ["+"]);
// (b) A registered incompatibility (P → Q) ⊥ (Q → P), yet both receive +.
assert.deepEqual(run((e) => {
  e.observeNegative("Bs", P, "np");
  e.observeNegative("Bs", Q, "nq");
  e.addIncompatibility("Bs", implies(P, Q), implies(Q, P));
}, [P, Q], [implies(P, Q), implies(Q, P)]), ["+", "+"]);
// (c) Short-circuit: with A excluded, the observed -(B → C) is never compared with v(B → C) = +.
assert.deepEqual(run((e) => {
  e.observeNegative("Bs", A, "na");
  e.observeNegative("Bs", B, "nb");
  e.observeNegative("Bs", C, "nc");
  e.observeNegative("Bs", implies(B, C), "nbc");
}, [A, B, C], [and(A, implies(B, C))]), ["-"]);
// (d) A handle outside Dom(B*) is accepted although (C3) asks for handles of Dom(B*).
const outside = atom("H", [{ role: "arg", handle: "zzz" }]);
assert.deepEqual(run((e) => e.observePositive("Bs", outside, "w"), [outside], [outside]), ["+"]);
```

#### R10: M1(i) refuses an independent criterion through a shared consequence; empty and mistargeted refinements pass

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, forall, implies } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("Swan", {
  nativeRelations: ["White", "Lake", "Alive", "Big"],
  handles: [
    { id: "swan_402", criterion: "I_Swan", kind: "contingent" },
    { id: "swan_101", criterion: "I_Swan", kind: "contingent" },
  ],
});
b.defineBoundary("Swan_Rest", { parents: ["Swan"], handleFilter: (h) => h.id !== "swan_402" });
b.defineBoundary("Swan_Same", { parents: ["Swan"] });
const rel = (name: string, h: string) => atom(name, [{ role: "subject", handle: h }]);
const auth = (h: string) => ({ handle: h, criterion: "I_Swan" });
const base = (): InquiryEngine => {
  const e = new InquiryEngine(b);
  e.observeNegative("Swan", rel("White", "swan_402"), "obs_black", auth("swan_402"));
  e.observePositive("Swan", rel("Lake", "swan_101"), "lake101", auth("swan_101"));
  e.observeNegative("Swan", rel("Lake", "swan_402"), "lake402", auth("swan_402"));
  return e;
};
const split = (e: InquiryEngine, to: string, target: string, criterion: string) =>
  e.refineBoundary({
    fromBoundary: "Swan",
    toBoundary: to,
    originalUniversal: forall("x", "Swan", rel("White", "x")),
    targetRelation: target,
    criterionItem: rel(criterion, "x"),
  });

// The criterion Lake is admitted on its own ...
assert.equal(split(base(), "Swan_Rest", "White", "Lake").ok, true);
// ... and refused once two background conditionals share a consequence.
const e = base();
e.observePositive("Swan", implies(rel("Lake", "swan_101"), rel("Alive", "swan_101")), "c1");
e.observePositive("Swan", implies(rel("White", "swan_101"), rel("Alive", "swan_101")), "c2");
const r = split(e, "Swan_Rest", "White", "Lake");
assert.equal(r.ok ? "admitted" : r.violation, "M1-circular");
// A target relation absent from the universal, and a refinement that excises nothing, are admitted.
assert.equal(split(base(), "Swan_Rest", "Big", "Lake").ok, true);
assert.equal(split(base(), "Swan_Same", "White", "Big").ok, true);
```

#### R11: Reusing an identifier erases an observation under `monotoneOnly`, and overwrites a theorem

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("B");
const e = new InquiryEngine(b, { monotoneOnly: true });
const [P, Q, X, Y] = ["P", "Q", "X", "Y"].map((n) => atom(n));

e.observeNegative("B", P, "w1");
assert.equal(e.evaluate([P]).localStatus("B", P), "Excluded");
assert.throws(() => e.retract("w1"), /forbidden/); // Retract is refused under monotoneOnly ...
e.observePositive("B", Q, "w1"); // ... but reusing the identifier erases the exclusion
assert.equal(e.evaluate([P]).localStatus("B", P), "Open");

e.recordTheorem("B", "+", X, "t1");
e.recordTheorem("B", "+", Y, "t1"); // the theorem identifier is overwritten as well
assert.equal(e.evaluate([X]).localStatus("B", X), "Open");
```

#### R12: Direct boundary edits split `evaluate` from `evaluateAtStage`, and directly registered covers cannot be withdrawn

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, or } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("B");
b.defineBoundary("C1", { parents: ["B"] });
b.defineBoundary("C2", { parents: ["B"] });
b.declareDisjoint("C1", "C2");
const e = new InquiryEngine(b);
e.witnessCover("B", ["C1", "C2"]);
const PQ = or(atom("P"), atom("Q"));
e.observePositive("C1", atom("P"), "p1");
e.observePositive("C2", atom("Q"), "q2");
// Direct boundary edits are no inquiry transition: the stage does not advance.
const stage = e.stage;
b.defineBoundary("B3", { parents: ["B"] });
b.declareDisjoint("B3", "C1");
b.declareDisjoint("B3", "C2");
assert.equal(e.stage, stage);
assert.equal(e.evaluate([PQ]).localStatus("B", PQ), "Open"); // the live boundary system
assert.equal(e.evaluateAtStage(stage, [PQ]).localStatus("B", PQ), "Grounded"); // the stage snapshot
// A cover registered directly on the boundary system cannot be withdrawn through the engine.
const direct = b.registerCover("C1", ["C1"]);
assert.equal(e.withdraw(direct), false);
```

#### R13: A reflection on an `Undetermined` record reads `Excluded`

```ts
import assert from "node:assert/strict";
import { BoundarySystem } from "./src/boundary.ts";
import { InquiryEngine } from "./src/engine.ts";
import { atom, refl } from "./src/syntax.ts";

const b = new BoundarySystem();
b.defineBoundary("B");
const e = new InquiryEngine(b);
const [P, Q, X] = ["P", "Q", "X"].map((n) => atom(n));
e.observePositive("B", P, "wp");
e.observePositive("B", Q, "wq");
e.addIncompatibility("B", P, Q); // a symmetric conflict: the authority of +P is undetermined
const t = e.stage;
assert.equal(e.evaluateAtStage(t, [P]).authorityOf("B", "+", P), "Undetermined");
e.observePositive("B", X, "later");
const reflection = refl(1, "B", "+", P, t);
assert.equal(e.evaluate([reflection]).localStatus("B", reflection), "Excluded"); // read as not Live
```
