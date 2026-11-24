---
title: UL-Core Formal Metatheory & Open Proof-Theoretic Boundaries
version: 0.1.0
status: active
date: 2026-11-25
---

# Formal Metatheory & Open Proof-Theoretic Boundaries (`UL-Core`)

This document formalizes the metatheoretic invariants of [core.md](core.md) (`v0.1.0`) and [worked-examples.md](worked-examples.md), separating ratified invariants (`Consensus`, backed by executable reference-kernel verification) from open proof-theoretic and semantic boundaries (`Exploratory`).

Per [AGENTS.md](../AGENTS.md) §2.5 & §4, `MT-1`–`MT-6`, `MT-8`, and `MT-9` carry `Consensus` status anchored to executable tests via `spec-guard`, while `MT-7` (open `M1(ii)` disguised contingent proxy boundary) remains `Exploratory` until that semantic definability boundary closes.

---

## 1. Well-Foundedness & Fixed-Point Semantics

1. `Consensus` **MT-1: Acyclic Grounding, Least-Fixpoint `Live` Authority & Stratified Quarantine** ([core.md](core.md) §3 items 8, 10; [`layer3-structural-rules-and-cut`](../docs/design-review.md#layer3-structural-rules-and-cut)):
   - **Statement**: Let `Entries(Σ)` be the finite set of derived and base ground entries generated in an inquiry state `Σ` over a finite signature and boundary system. Define `Live(Σ) ⊆ Entries(Σ)` as the least fixpoint `μL. F_Σ(L)` of the operator:
     ```text
     F_Σ(L) := { e ∈ Entries(Σ) | ¬obstructed_Σ(e) ∧ (base(e) ∨ structural(e) ∨ ∀d ∈ deps(e). d ∈ L) }
     ```
     where `obstructed_Σ(e)` holds iff there exists a non-empty `B' ⊑ boundary(e)` such that `(B', item(e))` is in local `Collision`. Then:
     1. `F_Σ` is monotone on `(𝒫(Entries(Σ)), ⊆)`, so by Knaster–Tarski `Live(Σ)` exists, is unique, and is reached in at most `|Entries(Σ)|` iterations (implemented in `src/engine.ts`).
     2. **Anti-Circularity**: Any mutual-support cycle `e₁ → e₂ → ... → e₁` with no unobstructed acyclic path back to `G⁺ ∪ G⁻ ∪ C_B` never enters `Live(Σ)`.
   - **Proof Sketch**: Monotonicity of `F_Σ` follows immediately because `¬obstructed_Σ(e)` does not depend on `L` and `∀d ∈ deps(e). d ∈ L` is positive in `L`. For anti-circularity, proceed by induction on Knaster–Tarski approximants `L_0 = ∅`, `L_{m+1} = F_Σ(L_m)`: if `C ⊆ Entries(Σ)` is a non-empty subset where every `e ∈ C` has some dependency `d ∈ deps(e) ∩ C`, no element of `C` can be the minimal-step entrant into any `L_m`, hence `C ∩ Live(Σ) = ∅`.
   - **Stratified Quarantine Resolution**: Under unstratified eager closure, a broad rule `B_all ⊩⁺ (A → C)` plus `B_all ⊩⁺ A` can emit a raw entry `e_C = (B_all, +C)` before `B_sub ⊩⁻ A` collides on `B_sub ⊑ B_all`, creating a **ghost collision** against an independent `B_sub ⊩⁻ C` (or emitting a ghost `+A` from a refuted conditional `X → A` when `+X ∧ -A` already holds). Ratified in [core.md](core.md) §3 item 10 and implemented in `src/engine.ts` via a **Van Gelder alternating fixpoint** over obstruction sets (`defObstructed` / `mayPass` / `defPass`), defeated premises and falsified conditionals never fire transmissive rules (`MP`, `∨E`, `⊥_B`, `≈_B`, `imposs-excl`), while symmetric conflicts and downward heredity records remain preserved.
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_dual_polarity_statuses_and_well_founded_dag_rejects_cycles" min="1" reason="Acyclic DAG provenance and least-fixpoint status evaluation are verified" -->
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_stratified_quarantine_eliminates_ghost_collisions_and_preserves_symmetric_conflict" min="1" reason="Van Gelder alternating fixpoint stratified quarantine eliminates ghost collisions" -->

---

## 2. Self-Reference & Triviality Resistance

2. `Consensus` **MT-2: Curry Firewall Soundness (Level Stratification & Mutual Strict Positivity)** ([core.md](core.md) §1 item 3; [worked-examples.md](worked-examples.md) §3; [`layer4-implication-and-curry-barrier`](../docs/design-review.md#layer4-implication-and-curry-barrier)):
   - **Statement**: Suppose every recursive item/boundary definition system `{X_i := F_i(X⃗)}` obeys:
     1. **Level Stratification**: Every reflection item `Refl_k(J)` occurring inside a level-`n` definition satisfies `level(J) ≤ k < n`; and
     2. **Mutual Strict Positivity**: In the directed dependency graph over `{X_i}`, no directed cycle traverses a **contravariant edge**—namely, passing to the left of `→`, inside an unguarded strong polarity flip `~` (that feeds a conditional or negative position), or inside a boundary promotion `[δ]` / quantifier domain constraint `D`.
     Then every admissible definition admits a well-founded denotational interpretation across the stratified hierarchy `M₀ ⊆ M₁ ⊆ ... ⊆ M_ω`, blocking Curry's Paradox (`⊢ Z` for arbitrary `Z`) across all four known attack vectors (`K := K → Z`, same-level `Refl` diagonal, `K := (~K) → Z`, and boundary-promotion `K := ∀(y : B ⊓ [K]) Z`).
   - **Proof Sketch**: Proceed by lexicographic induction on `(n, structural-depth)`:
     - Fix all evaluations `⊩⁺_k, ⊩⁻_k` at levels `k < n` (`M_{<n}`). Any `Refl_k(J)` with `k < n` acts as a fixed atomic predicate in `M_{<n}` whose positive/negative witness sets cannot shift while solving level `n`.
     - Within level `n`, contract non-contravariant DAG edges into finite strictly positive monotone operators over `(𝒫(Pos_n), 𝒫(Neg_n))` (note that `∧`, `∨`, right-hand side of `→`, and quantifier bodies preserve positivity). By Knaster–Tarski, each level-`n` recursive component admits a unique least fixpoint.
     - Vector 1 (`left-of-implies`), Vector 3 (`~` feeding `→`), and Vector 4 (`boundary-promotion`) each induce a self-loop with at least one contravariant edge and are syntactically rejected at formation time. Vector 2 fails same-level stratification (`n < n` impossible); well-typed cross-stage reflection `K_{t+1} := Refl_t(Σ_t ; B ⊩⁺ K_t) → Z` separates `K_t` from `K_{t+1}`, breaking Step 2 (`K ⊢ K → Z`) of the Curry derivation.
   - **Specification & Kernel Status**: Ratified in [core.md](core.md) §1 item 3 and enforced across `src/syntax.ts` (`checkRecursiveDefinitionSystem` across arbitrary finite definition dependency graphs, with `checkRecursiveDefinition` delegating to it), `src/engine.ts` (`evaluateAtStage` + immutable `#stageArchive` evaluating cross-stage reflection strictly against frozen `0 ≤ t < currentStage` and `level(J) ≤ k` with guaranteed finite termination), and `src/deduction.ts` (`refl-intro`).
   <!-- @assert-count target="test/syntax-and-curry.test.ts" symbol="function test_curry_firewall_blocks_all_four_vectors_and_allows_cross_stage" min="1" reason="Single-definition Curry firewall and cross-stage reflection are verified" -->
   <!-- @assert-count target="test/syntax-and-curry.test.ts" symbol="function test_mutual_recursion_curry_firewall_and_positive_systems" min="1" reason="Mutual-recursion Strict Positivity and cross-definition stratification are verified" -->
   <!-- @assert-count target="test/reflection.test.ts" symbol="function test_cross_stage_reflection_trace_and_historical_immutability" min="1" reason="Cross-stage historical archive immutability and nested level reflection are verified" -->
   <!-- @assert-count target="test/reflection.test.ts" symbol="function test_cross_stage_reflection_curry_immunity_and_deduction_stratification" min="1" reason="Operational Vector 2 Curry immunity and deduction refl-intro stratification are verified" -->

3. `Consensus` **MT-3: Non-Explosion & Non-Witnessing of `⊥` on Non-Empty Boundaries** ([core.md](core.md) §1 item 1, §2 item 4, §3 items 10–12; [`layer1-collision-quarantine`](../docs/design-review.md#layer1-collision-quarantine)):
   - **Statement**:
     1. **Global Non-Explosion**: If `(B, A)` enters `Collision` in state `Σ`, arbitrary unrelated items `Z` are **not** derivable (`B ⊩⁺ Z` does not follow from `Collision` on `(B, A)` alone).
     2. **Non-Witnessing of `⊥` (`Live` Safety)**: Under base admissibility (`⊥ ∉ G⁺`), no non-empty boundary `B ≠ ⊥_B` ever holds a `Live` positive witness `Σ ; B ⊩⁺ ⊥ [π]`.
   - **Proof Sketch**:
     - Part 1 follows by direct structural induction on the derivation calculus in [core.md](core.md) §3 items 9–12: no introduction rule accepts a pair `(⊩⁺ A, ⊩⁻ A)` as premises for an arbitrary conclusion `Z`. Rather, `Collision` sets `obstructed(B, A)` and removes `(B, A)` and its descendants from `Live(Σ)`.
     - Part 2 follows because `Σ ; B ⊩⁻ ⊥` holds structurally on every non-empty `B ≠ ⊥_B` ([core.md](core.md) §3 item 12). Thus, even if some chain yields a raw entry `(B, +⊥)`, `(B, ⊥)` immediately enters `Collision` and is non-`Live`. Furthermore, when `+(A → ⊥)` originates from structural boundary collapse (`B ⊓ [A] = ⊥_B`) or `Live`-gated `imposs-excl`, `B ⊩⁻ A` is induced directly, putting any competing `+A` in `Collision` before `Scoped Cut` (`MP`) can derive `+⊥`.
   - **Specification & Kernel Status**: Ratified in [core.md](core.md) §3 item 12 and enforced in `src/engine.ts`, which explicitly rejects direct `Observe⁺(B, ⊥)` on non-empty boundaries and implements `Live`-gated `imposs-excl` (`+(A → ⊥) ⟹ -A`) without enabling Double Negation Elimination (`(A → ⊥) → ⊥ ⊬ A`). Combined with Van Gelder stratification (`MT-1`), conflicting `Observe⁺(B, A → ⊥)` and `Observe⁺(B, A)` collides `(B, A → ⊥)` via `counter-implies` before `MP` can fire, emitting zero `+⊥` entries.
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_structural_rules_scoped_cut_and_horizontal_contraction" min="1" reason="Non-Explosion and Scoped Cut blocking under intermediate collision are verified" -->
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_bottom_non_witnessing_guard_and_imposs_contraposition" min="1" reason="Base bottom guard, Live non-witnessing of bottom, and imposs-excl without DNE are verified" -->

---

## 3. Boundary Algebra, Disjoint Isolation & Cover Stability

4. `Consensus` **MT-4: Disjoint Regime Zero-Leakage & Selective Quarantine Survival** ([core.md](core.md) §2 item 4, §3 items 9–10; [worked-examples.md](worked-examples.md) §1):
   - **Statement**: Suppose `B₁, B₂ ≠ ⊥_B` are disjoint (`B₁ ⊓ B₂ = ⊥_B`). Suppose further that `Σ₁` extends `Σ₀` solely by adding a counterexample `Observe⁻(B₂, A, w)` (or derived exclusions native to `B₂`). Then:
     1. **Zero Negative Leakage**: For every non-empty sub-boundary `B' ⊑ B₁`, the exclusion `B₂ ⊩⁻ A` cannot inherit onto `B'`.
     2. **Local Non-Obstruction**: `(B₁, A)` itself is not obstructed by `Collision` on `(B₂, A)`.
     3. **Selective Survival**: Every ground `(B₁, ±Y [π])` that was `Live` in `Σ₀` and whose provenance DAG `π` contains no node `(B_sup, X)` with `B₂ ⊑ B_sup` remains `Live` in `Σ₁`.
   - **Proof Sketch**:
     - For (1), downward heredity transfers entries only to non-empty `B' ⊑ B₂`. Any `B'` with both `B' ⊑ B₁` and `B' ⊑ B₂` satisfies `B' ⊑ B₁ ⊓ B₂ = ⊥_B`, contradicting `B' ≠ ⊥_B`.
     - For (2), obstruction propagates strictly upward along `⊑` (a collision on `B_col` obstructs `(B_ext, A)` iff `B_col ⊑ B_ext`). Since `B₂ ⊑ B₁` would yield `⊥_B = B₁ ⊓ B₂ = B₂ ≠ ⊥_B` (contradiction), `B₂ ⋢ B₁`.
     - For (3), any node `(B_node, X)` in `π` with `B₂ ⋢ B_node` cannot become `obstructed` by any collision at or below `B₂`; by structural induction over the acyclic DAG `π`, every dependency in `π` remains in `Live(Σ₁)`, so `(B₁, ±Y [π]) ∈ Live(Σ₁)`.
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_symmetric_downward_heredity_and_disjoint_zero_leakage" min="1" reason="Disjoint regime zero negative leakage is verified" -->
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_quarantine_upstream_obstruction_and_selective_survival" min="1" reason="Upstream obstruction and selective quarantine survival are verified" -->

5. `Consensus` **MT-5: Meet-Stability of Cover-Witnessed Disjunction (`D2`) & Soundness of `∨E` Gluing** ([core.md](core.md) §2 item 5, §3 item 12; [`layer4-conjunction-disjunction-and-covers`](../docs/design-review.md#layer4-conjunction-disjunction-and-covers)):
   - **Statement**:
     1. **Downward Heredity of `D2` Disjunction**: If `Σ ; B ⊩⁺ (A ∨ C) [π]` is grounded by a witnessed exhaustive cover `{B₁, ..., B_k} ▷ B`, then for every non-empty sub-boundary `B' ⊑ B`, `{B_i ⊓ B' | B_i ⊓ B' ≠ ⊥_B} ▷ B'` witnesses `Σ ; B' ⊩⁺ (A ∨ C)`.
     2. **Soundness of Cover Gluing (`∨E`)**: From `Live` `B ⊩⁺ (A ∨ C)` (via `{B_i} ▷ B`), `Live` `B ⊩⁺ (A → E)`, and `Live` `B ⊩⁺ (C → E)`, every cell `B_i` acquires a `Live` witness `B_i ⊩⁺ E`, justifying `B ⊩⁺ E`.
   - **Proof Sketch**:
     - By Axiom 3 (Meet-Stability, [core.md](core.md) §2 item 5), `{B_i ⊓ B' | B_i ⊓ B' ≠ ⊥_B}` is a witnessed exhaustive cover of `B'`; by Axiom 5 (Non-Vacuity) and `B' ≠ ⊥_B`, this cover contains at least one non-empty cell `B_j ⊓ B'`. On each such cell `B_j ⊓ B' ⊑ B_j`, downward heredity (`§3 item 9`) inherits whichever of `B_j ⊩⁺ A` or `B_j ⊩⁺ C` held on `B_j`.
     - For `∨E`, downward heredity restricts both `B ⊩⁺ (A → E)` and `B ⊩⁺ (C → E)` to every cell `B_i ⊑ B`. Since each non-empty `B_i` has a `Live` witness for either `A` or `C`, `Scoped Cut` (`B_i ⊓ B_i = B_i ≠ ⊥_B`) produces `B_i ⊩⁺ E` on every cell of `{B_i} ▷ B`. Gluing across the exhaustive cover `{B_i} ▷ B` grounds `B ⊩⁺ E`.
   - **Standalone Gluing Status**: Ratified in [core.md](core.md) §3 item 12 and implemented both in `src/engine.ts` (`Rule I`, across both polarities) and as the `cover-glue` rule in `src/deduction.ts`, preserving Quarantine obstruction and selective base-leaf provenance.
   <!-- @assert-count target="test/boundary-and-inquiry.test.ts" symbol="function test_finitary_grothendieck_covers_meet_stability_and_non_vacuity" min="1" reason="Finitary Grothendieck cover Meet-Stability and Non-Vacuity are verified" -->
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_connective_and_quantifier_polarity_rules_with_cover_gluing" min="1" reason="Cover-witnessed D2 disjunction and vE cover gluing soundness are verified" -->
   <!-- @assert-count target="test/deduction.test.ts" symbol="function test_standalone_cover_gluing_and_quarantine_propagation" min="1" reason="Standalone Cover-Gluing over witnessed covers and Quarantine obstruction are verified" -->

---

## 4. Inquiry Dynamics & Anti-Immunization

6. `Consensus` **MT-6: Polarity Purity of `Retract`, Reinstatement & Vertical Non-Commutativity** ([core.md](core.md) §2 item 7; [`layer4-negation-vs-exclusion`](../docs/design-review.md#layer4-negation-vs-exclusion)):
   - **Statement**:
     1. **Pure Cancellation (Sanskrit *prasajya-pratiṣedha*)**: Applying `Retract(g)` strictly deletes `g` from `G⁺ ∪ G⁻` without adding any element to either `G⁺` or `G⁻`. In particular, if `(B, A)` was `Grounded` (resp. `Excluded`) in `Σ` solely via a unique base leaf `g`, then in `Retract(g)(Σ)` the status of `(B, A)` becomes `Open`, never `Excluded` (resp. `Grounded`).
     2. **Quarantine Reinstatement**: If `(B, A)` was in `Collision` between `+A [g⁺]` and `-A [g⁻]`, then `Retract(g⁻)` removes the collision and restores `Live` authority to `+A [g⁺]` and any downstream derivations depending solely on `g⁺` and other `Live` leaves (without adding new positive leaves).
     3. **Vertical Non-Commutativity**: Vertical transition sequences `Σ₀ → Σ₁ → Σ₂` violate `Exchange` (`Observe⁺(B, A, w); Retract(w)` differs from `Retract(w); Observe⁺(B, A, w)`).
   - **Proof Sketch**: Immediate from the state transition definition (`§2 item 7`): `Retract(g)` modifies `Σ = (G⁺, G⁻, C_B, O_rev)` solely by set difference on `G⁺ ∪ G⁻` and re-evaluation of derived provenance. Since every derived entry for `±A` requires at least one base leaf in `G⁺ ∪ G⁻` (or structural `C_B`) by MT-1, deleting the sole base leaf eliminates all derived entries on that polarity without constructing an opposite-polarity leaf. Counterexample for (3): starting from `Open` `(B, A)` with `w ∉ G⁺`, `Observe⁺(B, A, w); Retract(w)` ends in `Open`, whereas `Retract(w); Observe⁺(B, A, w)` leaves `(B, A)` `Grounded`.
   <!-- @assert-count target="test/boundary-and-inquiry.test.ts" symbol="function test_inquiry_updates_retract_non_commutativity_and_m1_m2" min="1" reason="Pure Retract, vertical non-commutativity, and Quarantine reinstatement are verified" -->

7. `Exploratory` **MT-7: `M1` + `M2` Anti-Immunization Guarantees & Proxy-Excision Boundary** ([core.md](core.md) §2 item 7; [worked-examples.md](worked-examples.md) §2; [`layer3-boundary-composition`](../docs/design-review.md#layer3-boundary-composition), [`layer5-content-and-coreference`](../docs/design-review.md#layer5-content-and-coreference)):
   - **Statement**: Let `Σ` contain counterexample `B ⊩⁻ A(w)` (`w ∈ Dom(B)` verified under `I_B`), putting `(B, ∀(x : B) A(x))` into `Excluded` or `Collision`. Then any transition `RefineBoundary(B → B' = B ⊓ [δ])` admitted by `M1 + M2` guarantees:
     1. **Non-Erasure (`M2`)**: `(B, ∀(x : B) A(x))` remains `Excluded` in every downstream state unless `w` itself is explicitly withdrawn via `Retract`.
     2. **Non-Circularity (`M1(i)`)**: `δ` introduces zero direct or indirect dependence on the target relation of `A`, eliminating tautological immunizations such as `δ(x) := A(x)`.
     3. **Non-Contingency Against Named Handles (`M1(ii)`)**: `δ` contains no contingent handle reference (`kind === "contingent"`), blocking bare extensional excision `δ(x) := ~(x ≈_B w)` while permitting structurally defined singularities (`AddId(x)` for `ℝ \ {0}`).
   - **Disguised Contingent Proxy Boundary (Open Tension)**: Syntactic handle-kind tagging (`structural` vs. `contingent` in `src/boundary.ts` / `src/engine.ts`) blocks explicit handle excision (`x ≉_B swan_402`), **but** does not automatically prevent an agent from conjoining multiple contingent empirical predicates (e.g., `~FoundInLake7(x) ∨ ~TaggedOnTuesday(x)`) that extensionally excise only `swan_402` without naming its identifier. Full semantic resistance to proxy immunization relies on requiring `δ` to carry independent cross-handle predictivity ([worked-examples.md](worked-examples.md) §2 Attempt 3) or explicit methodological review.

---

## 5. Four-Tier Specialization & Classical Recovery

8. `Consensus` **MT-8: Soundness & Syntactic Completeness of `UL-Minimal` and `UL-Intuitionistic` (`⊥ → C`)** ([core.md](core.md) §4 item 13; [`layer2-classical-boundary-recovery`](../docs/design-review.md#layer2-classical-boundary-recovery)):
   - **Statement**:
     1. **`UL-Minimal` Specialization**: Under monotone `Σ` (forbidding `Retract`) and `No-Gluts` (zero collisions across `(B, X)`), every grounded derivation in `UL-Core` satisfies `Live(Σ)`, Quarantine never triggers, `Scoped Cut` equals unrestricted `Cut`, and the positive fragment over `{∧, ∨, →, ∀, ∃, ⊥, ~}` validates **Minimal Constructive Logic** (`NJ_min`) augmented with Nelson-style strong negation `~A` (`(A → ⊥) → ⊥ ⊬ A` and `⊬ A ∨ ~A`).
     2. **Conservative `UL-Intuitionistic` Extension**: Adding the boundary axiom `B ⊩⁺ (⊥ → C)` for every item `C` preserves soundness (`No-Gluts`) and yields **Heyting Intuitionistic First-Order Logic** (`NJ`) under finitary Beth-cover semantics ([core.md](core.md) §2 item 5, §3 item 12).
   - **Proof Sketch**:
     - Under `No-Gluts`, `collisions = ∅`, so `obstructed_Σ(e)` is identically false; by MT-1, every well-founded entry in `Entries(Σ)` lies in `Live(Σ)`. Consequently `Scoped Cut` applies unconditionally across overlapping boundaries. Since `∨` requires a witnessed cover (`D2`) and structural impossibility (`A → ⊥`) induces only `-A` without double-negation elimination, neither `A ∨ ~A` nor `(A → ⊥) → ⊥ ⊢ A` is derivable on an `Open` item.
     - Under `UL-Intuitionistic`, `B ⊩⁻ ⊥` holds structurally for all `B ≠ ⊥_B` (`MT-3`), so `No-Gluts` implies no ground `B ⊩⁺ ⊥` exists on any non-empty `B`. Therefore Modus Ponens with `⊥ → C` can never fire to manufacture `B ⊩⁺ C` or create a new collision.
   - **Syntactic Natural Deduction & Completeness Status**: Ratified in [core.md](core.md) §3 item 12 and implemented in `src/deduction.ts`, which provides a full Prawitz-style proof checker (`→I` hypothetical sub-proof discharge, `→E`, `∧I`/`∧E`, `∨I`/`∨E`, open-domain schematic `∀I` with strict eigenvariable freshness, `∀E`, `∃I`, `∃E` non-escape, standalone `Cover-Gluing`, `≈_B`, and `UL-Intuitionistic`-gated `⊥E`), recovering syntactic `UL-Minimal` (`NJ_min`) and `UL-Intuitionistic` (`NJ`) proof systems alongside Beth-cover semantics.
   <!-- @assert-count target="test/deduction.test.ts" symbol="function test_natural_deduction_implies_intro_and_anti_vacuity_quarantine" min="1" reason="Hypothetical implies-intro discharge, anti-vacuity, and Quarantine bridge are verified" -->
   <!-- @assert-count target="test/deduction.test.ts" symbol="function test_schematic_forall_intro_eigenvariable_soundness_on_open_domains" min="1" reason="Open-domain schematic forall-intro and exists-elim eigenvariable rules are verified" -->
   <!-- @assert-count target="test/deduction.test.ts" symbol="function test_ul_minimal_vs_ul_intuitionistic_proof_theoretic_separation" min="1" reason="Proof-theoretic separation between UL-Minimal and UL-Intuitionistic is verified" -->

9. `Consensus` **MT-9: `UL-Classical` Bivalent Recovery (`2` on Atomic `B*` and `2^k` on Atomic Covers)** ([core.md](core.md) §4 item 13; [worked-examples.md](worked-examples.md) §4; [`scope-anchor-unified-core`](../docs/design-review.md#scope-anchor-unified-core)):
   - **Statement**: Freeze `Σ`, restrict to object level `n = 0`, fix finest congruence `≈_{B*}`, and assume `No-Gluts` (`⊩⁺` and `⊩⁻` are disjoint) and `No-Gaps` (every base atom/congruence on every atomic cell `B* ≠ ⊥_B` is either `Grounded` or `Excluded`).
     1. **Atomic Cell Recovery (`2`)**: On a single non-empty atomic cell `B*`, the status map `v_{B*}(A) := 1` iff `B* ⊩⁺ A` (and `0` iff `B* ⊩⁻ A`) extends uniquely by structural induction over all level-`0` closed items `A` to a **Tarskian classical first-order valuation**:
        - **Bivalence**: Every `A` is strictly `Grounded (+)` or `Excluded (-)`; no item is `Open` or `Collision`.
        - **Negation Collapse**: `~A` and `A → ⊥` take identical truth values (`¬v_{B*}(A)`), yielding Double Negation Elimination.
        - **Safe Material Implication**: `v_{B*}(A → C) = max(1 - v_{B*}(A), v_{B*}(C))`, while `No-Gluts` prevents `MP` from firing when `v_{B*}(A) = 0`.
        - **Excluded Middle, Quantifiers & Equality**: `v_{B*}(A ∨ ~A) = 1`, `∀`/`∃` obey classical duality over `Dom(D)`, and `≈_{B*}` satisfies Leibnizian substitutivity over all native relations.
        - **Vacuous Explosion**: `{ A, ~A } ⊨_{B*} C` holds vacuously because no `UL-Classical` state satisfies both `+A` and `-A` (`No-Gluts`).
     2. **Finite Cover Recovery (`2^k`)**: On a non-atomic boundary `B` partitioned by a witnessed finite atomic cover `{B*₁, ..., B*_k} ▷ B`, `UL-Core` with `D2` disjunction recovers the **finite Boolean product algebra `2^k`**: an item `A` holds globally on `B` (`B ⊩⁺ A`) iff `v_{B*_i}(A) = 1` for all `i ∈ {1, ..., k}`, and every classical tautology (e.g., `B ⊩⁺ (A ∨ ~A)`) holds globally via `D2` even when `A` splits across atomic cells ([worked-examples.md](worked-examples.md) Derivation 4A).
   - **Proof Sketch**: Structural induction on `A` on atomic `B*`:
     - *Base*: `atom` and `equiv` satisfy `No-Gaps` and `No-Gluts` by assumption; `bottom` satisfies `B* ⊩⁻ ⊥` and (by MT-3 + `No-Gluts`) never `B* ⊩⁺ ⊥`, hence `v_{B*}(⊥) = 0`.
     - *Inductive Step*:
       - `~A`: [core.md](core.md) §3 item 12 gives `+(~A) ⟺ -A` and `-(~A) ⟺ +A`, flipping `{1, 0}` identically.
       - `A ∧ C` and `A ∨ C`: On atomic `B*`, the sole non-vacuous witnessed cover is `{B*}` itself (`Axiom 1 & 2 & 5`), so `D2` collapses to `v_{B*}(A ∨ C) = max(v_{B*}(A), v_{B*}(C))`, while `∧` gives `min`.
       - `A → C`: §3 item 12 defines `B* ⊩⁻ (A → C) ⟺ B* ⊩⁺ A ∧ B* ⊩⁻ C`, i.e., `(1, 0)`. In all other three `(A, C)` combinations `(0,0), (0,1), (1,1)`, `-(A → C)` fails (`No-Gluts`), so `No-Gaps` closes `(B*, A → C)` to `+(A → C)`. Crucially, when `v_{B*}(A) = 0`, `No-Gluts` blocks `B* ⊩⁺ A`, so `MP` never fires.
       - `A → ⊥`: Specializing `C = ⊥` (`v_{B*}(⊥) = 0`) yields `-(A → ⊥) ⟺ +A`, so by `No-Gaps` + `No-Gluts`, `+(A → ⊥) ⟺ -A ⟺ +(~A)`.
       - `∀(x : D) A(x)` / `∃(x : D) A(x)` over closed `Dom(D)`: By IH on every `w ∈ Dom(D)`, `v_{B*}(A(w)) ∈ {0, 1}`, yielding classical universal/existential clauses and De Morgan duality.
     - *Multi-Cell Cover `2^k`*: Since `{B*₁, ..., B*_k} ▷ B` is a cover of atomic cells, any classical tautology `T` evaluates to `1` on every `B*_i`; for disjunctions such as `A ∨ ~A`, each cell `B*_i` holds either `+A` or `+(~A)`, directly witnessing `D2` disjunction `B ⊩⁺ (A ∨ ~A)` (`2^k` global truth).
   - **Specification & Kernel Status**: Ratified in [core.md](core.md) §4 item 13 and implemented in `src/specializations.ts` via `GlobalCoverStatus` (`"+" | "-" | "split"`) alongside per-cell `cellPolarities` in `ClassicalValuation`, faithfully reporting the `2^k` product Boolean algebra without conflating contingent split items across atomic cells with globally excluded items.
   <!-- @assert-count target="test/specializations.test.ts" symbol="function test_four_tier_deductive_spectrum_and_classical_recovery" min="1" reason="UL-Classical atomic bivalence, negation collapse, and safe material implication are verified" -->
   <!-- @assert-count target="test/specializations.test.ts" symbol="function test_classical_atomic_cover_2k_boolean_algebra_reporting" min="1" reason="Multi-cell 2^k Boolean product algebra reporting is verified" -->

---

## 6. Open Metatheoretic Tensions & Audit Summary

| ID | Finding | Affected Theorems | Spec / Kernel Status |
| :--- | :--- | :--- | :--- |
| **G-1** | **Ghost Collision Under Eager Closure**: Eliminating dead-branch ghost collisions via Van Gelder alternating fixpoint over obstruction sets. | MT-1 | **Resolved** — stratified quarantine ratified in [core.md](core.md) §3 item 10 and verified in `src/engine.ts` + tests. |
| **G-2** | **Mutual Recursion in Strict Positivity**: Extending Curry firewall cycle and stratification checks across finite definition systems. | MT-2 | **Resolved** — ratified in [core.md](core.md) §1 item 3 and verified via `checkRecursiveDefinitionSystem` in `src/syntax.ts` + tests. |
| **G-3** | **`Observe⁺(B, ⊥)` & Unsourced `+(A → ⊥)` Tension**: Rejecting direct `Observe⁺(B, ⊥)`, gating `imposs-excl` (`+(A → ⊥) ⟹ -A`), and blocking `+⊥` under `Collision`. | MT-3 | **Resolved** — `⊥ ∉ G⁺`, `Live` non-witnessing, and `imposs-excl` ratified in [core.md](core.md) §3 item 12 and verified in `src/engine.ts` + tests. |
| **G-4** | **Syntactic `→I` / Schematic `∀I` & Standalone Cover-Gluing**: Prawitz-style proof verification and sheaf gluing beyond finite domain evaluation. | MT-5, MT-8 | **Resolved** — `src/deduction.ts`, `src/engine.ts`, and ratified rules in [core.md](core.md) §3 item 12 (`MT-8` promoted to `Consensus`). |
| **G-5** | **`2^k` Output Collapse & Disguised Contingent Proxies**: Reporting `GlobalCoverStatus` (`split`) + `cellPolarities` vs. `M1(ii)` semantic proxy immunization. | MT-7, MT-9 | **`2^k` resolved** (ratified in [core.md](core.md) §4 item 13 and verified in `src/specializations.ts` + tests); `M1(ii)` semantic proxy definability remains **open** (keeps `MT-7` `Exploratory`). |
