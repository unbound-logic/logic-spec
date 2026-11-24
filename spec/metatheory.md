---
title: UL-Core Formal Metatheory & Open Proof-Theoretic Boundaries
version: 0.1.0-draft
status: draft
date: 2026-11-25
---

# Formal Metatheory & Open Proof-Theoretic Boundaries (`UL-Core`)

This draft document investigates what metatheoretic invariants actually hold of [core.md](core.md) (`v0.1.0`) and [worked-examples.md](worked-examples.md), where semantic guarantees currently outrun syntactic proof rules, and where formalization uncovered genuine tensions requiring future specification or kernel tightening.

Per [AGENTS.md](../AGENTS.md) §2.5 & §4, all theorems below carry the `Exploratory` status label pending maintainer review and ratification; none should be treated as settled `Consensus` until ratified and bound to executable checks or formal proof artifacts.

---

## 1. Well-Foundedness & Fixed-Point Semantics

1. `Exploratory` **MT-1: Acyclic Grounding, Least-Fixpoint `Live` Authority & Stratified Quarantine** ([core.md](core.md) §3 items 8, 10; [`layer3-structural-rules-and-cut`](../docs/design-review.md#layer3-structural-rules-and-cut)):
   - **Statement**: Let `Entries(Σ)` be the finite set of derived and base ground entries generated in an inquiry state `Σ` over a finite signature and boundary system. Define `Live(Σ) ⊆ Entries(Σ)` as the least fixpoint `μL. F_Σ(L)` of the operator:
     ```text
     F_Σ(L) := { e ∈ Entries(Σ) | ¬obstructed_Σ(e) ∧ (base(e) ∨ structural(e) ∨ ∀d ∈ deps(e). d ∈ L) }
     ```
     where `obstructed_Σ(e)` holds iff there exists a non-empty `B' ⊑ boundary(e)` such that `(B', item(e))` is in local `Collision`. Then:
     1. `F_Σ` is monotone on `(𝒫(Entries(Σ)), ⊆)`, so by Knaster–Tarski `Live(Σ)` exists, is unique, and is reached in at most `|Entries(Σ)|` iterations (implemented in `src/engine.ts`).
     2. **Anti-Circularity**: Any mutual-support cycle `e₁ → e₂ → ... → e₁` with no unobstructed acyclic path back to `G⁺ ∪ G⁻ ∪ C_B` never enters `Live(Σ)`.
   - **Proof Sketch**: Monotonicity of `F_Σ` follows immediately because `¬obstructed_Σ(e)` does not depend on `L` and `∀d ∈ deps(e). d ∈ L` is positive in `L`. For anti-circularity, proceed by induction on Knaster–Tarski approximants `L_0 = ∅`, `L_{m+1} = F_Σ(L_m)`: if `C ⊆ Entries(Σ)` is a non-empty subset where every `e ∈ C` has some dependency `d ∈ deps(e) ∩ C`, no element of `C` can be the minimal-step entrant into any `L_m`, hence `C ∩ Live(Σ) = ∅`.
   - **Ghost-Collision Subtlety (Open Tension)**: In an eager closure loop that populates raw `Entries(Σ)` across iterations before quarantining colliding premises (the pattern used in `src/engine.ts`), a broad rule `B_all ⊩⁺ (A → C)` plus `B_all ⊩⁺ A` can emit a raw entry `e_C = (B_all, +C)` before `B_sub ⊩⁻ A` triggers a `Collision` on `B_sub ⊑ B_all`. Even though `e_C` subsequently loses `Live` status, if raw collision detection inspects *all* entries regardless of grounding status, `Down(B_all→B_sub, e_C)` creates a **ghost collision** against an otherwise valid independent `B_sub ⊩⁻ C`—falsely obstructing `(B_all, -C)` and spawning a spurious `Rev(B_sub, C)`. Eliminating ghost collisions requires stratifying collision detection over unquarantined / non-ghost derivations rather than over unpruned eager raw entries.

---

## 2. Self-Reference & Triviality Resistance

2. `Exploratory` **MT-2: Curry Firewall Soundness (Level Stratification & Mutual Strict Positivity)** ([core.md](core.md) §1 item 3; [worked-examples.md](worked-examples.md) §3; [`layer4-implication-and-curry-barrier`](../docs/design-review.md#layer4-implication-and-curry-barrier)):
   - **Statement**: Suppose every recursive item/boundary definition system `{X_i := F_i(X⃗)}` obeys:
     1. **Level Stratification**: Every reflection item `Refl_k(J)` occurring inside a level-`n` definition satisfies `level(J) ≤ k < n`; and
     2. **Mutual Strict Positivity**: In the directed dependency graph over `{X_i}`, no directed cycle traverses a **contravariant edge**—namely, passing to the left of `→`, inside an unguarded strong polarity flip `~` (that feeds a conditional or negative position), or inside a boundary promotion `[δ]` / quantifier domain constraint `D`.
     Then every admissible definition admits a well-founded denotational interpretation across the stratified hierarchy `M₀ ⊆ M₁ ⊆ ... ⊆ M_ω`, blocking Curry's Paradox (`⊢ Z` for arbitrary `Z`) across all four known attack vectors (`K := K → Z`, same-level `Refl` diagonal, `K := (~K) → Z`, and boundary-promotion `K := ∀(y : B ⊓ [K]) Z`).
   - **Proof Sketch**: Proceed by lexicographic induction on `(n, structural-depth)`:
     - Fix all evaluations `⊩⁺_k, ⊩⁻_k` at levels `k < n` (`M_{<n}`). Any `Refl_k(J)` with `k < n` acts as a fixed atomic predicate in `M_{<n}` whose positive/negative witness sets cannot shift while solving level `n`.
     - Within level `n`, contract non-contravariant DAG edges into finite strictly positive monotone operators over `(𝒫(Pos_n), 𝒫(Neg_n))` (note that `∧`, `∨`, right-hand side of `→`, and quantifier bodies preserve positivity). By Knaster–Tarski, each level-`n` recursive component admits a unique least fixpoint.
     - Vector 1 (`left-of-implies`), Vector 3 (`~` feeding `→`), and Vector 4 (`boundary-promotion`) each induce a self-loop with at least one contravariant edge and are syntactically rejected at formation time. Vector 2 fails same-level stratification (`n < n` impossible); well-typed cross-stage reflection `K_{t+1} := Refl_t(Σ_t ; B ⊩⁺ K_t) → Z` separates `K_t` from `K_{t+1}`, breaking Step 2 (`K ⊢ K → Z`) of the Curry derivation.
   - **Implementation Gap**: `src/syntax.ts` (`checkRecursiveDefinition`) enforces Level Stratification and Strict Positivity for **single self-referential definitions** (`X := F(X)`), but does not yet check mutual-recursion cycles across multiple named definitions (`X := Y → Z`, `Y := X`).

3. `Exploratory` **MT-3: Non-Explosion & Non-Witnessing of `⊥` on Non-Empty Boundaries** ([core.md](core.md) §1 item 1, §2 item 4, §3 items 10–12; [`layer1-collision-quarantine`](../docs/design-review.md#layer1-collision-quarantine)):
   - **Statement**:
     1. **Global Non-Explosion**: If `(B, A)` enters `Collision` in state `Σ`, arbitrary unrelated items `Z` are **not** derivable (`B ⊩⁺ Z` does not follow from `Collision` on `(B, A)` alone).
     2. **Non-Witnessing of `⊥` (`Live` Safety)**: Under base admissibility (`⊥ ∉ G⁺`), no non-empty boundary `B ≠ ⊥_B` ever holds a `Live` positive witness `Σ ; B ⊩⁺ ⊥ [π]`.
   - **Proof Sketch**:
     - Part 1 follows by direct structural induction on the derivation calculus in [core.md](core.md) §3 items 9–12: no introduction rule accepts a pair `(⊩⁺ A, ⊩⁻ A)` as premises for an arbitrary conclusion `Z`. Rather, `Collision` sets `obstructed(B, A)` and removes `(B, A)` and its descendants from `Live(Σ)`.
     - Part 2 follows because `Σ ; B ⊩⁻ ⊥` holds structurally on every non-empty `B ≠ ⊥_B` ([core.md](core.md) §3 item 12). Thus, even if some chain yields a raw entry `(B, +⊥)`, `(B, ⊥)` immediately enters `Collision` and is non-`Live`. Furthermore, when `+(A → ⊥)` originates from structural boundary collapse (`B ⊓ [A] = ⊥_B`), [core.md](core.md) §3 item 12 simultaneously derives `B ⊩⁻ A`, putting any competing `+A` in `Collision` before `Scoped Cut` (`MP`) can derive `+⊥`.
   - **Unsourced `+(A → ⊥)` & `Observe⁺(B, ⊥)` Tension (Open Spec/Kernel Gap)**: Two subtle edge cases require explicit specification discipline:
     - First, [core.md](core.md) §3 item 12 states "`⊩⁺ ⊥` never holds on any `B ≠ ⊥_B`", while `src/engine.ts` rejects `Observe⁺(⊥_B, A)` (Non-Witnessing of `⊥_B`) yet does **not** reject `Observe⁺(B, ⊥)` (`bot`) on non-empty `B ≠ ⊥_B`.
     - Second, if an inquiry state permits an arbitrary base `Observe⁺(B, A → ⊥)` without enforcing the structural-impossibility inverse rule (`+(A → ⊥) ⟹ -A`), then adding `Observe⁺(B, A)` allows `MP` to emit a collided raw entry `B ⊩⁺ ⊥`. Either base assertions of `⊥` and raw `+(A → ⊥)` (without `-A`) must be barred at observation time, or [core.md](core.md) §3 item 12 must explicitly scope "`⊩⁺ ⊥` never holds" to **`Live` grounds**.

---

## 3. Boundary Algebra, Disjoint Isolation & Cover Stability

4. `Exploratory` **MT-4: Disjoint Regime Zero-Leakage & Selective Quarantine Survival** ([core.md](core.md) §2 item 4, §3 items 9–10; [worked-examples.md](worked-examples.md) §1):
   - **Statement**: Suppose `B₁, B₂ ≠ ⊥_B` are disjoint (`B₁ ⊓ B₂ = ⊥_B`). Suppose further that `Σ₁` extends `Σ₀` solely by adding a counterexample `Observe⁻(B₂, A, w)` (or derived exclusions native to `B₂`). Then:
     1. **Zero Negative Leakage**: For every non-empty sub-boundary `B' ⊑ B₁`, the exclusion `B₂ ⊩⁻ A` cannot inherit onto `B'`.
     2. **Local Non-Obstruction**: `(B₁, A)` itself is not obstructed by `Collision` on `(B₂, A)`.
     3. **Selective Survival**: Every ground `(B₁, ±Y [π])` that was `Live` in `Σ₀` and whose provenance DAG `π` contains no node `(B_sup, X)` with `B₂ ⊑ B_sup` remains `Live` in `Σ₁`.
   - **Proof Sketch**:
     - For (1), downward heredity transfers entries only to non-empty `B' ⊑ B₂`. Any `B'` with both `B' ⊑ B₁` and `B' ⊑ B₂` satisfies `B' ⊑ B₁ ⊓ B₂ = ⊥_B`, contradicting `B' ≠ ⊥_B`.
     - For (2), obstruction propagates strictly upward along `⊑` (a collision on `B_col` obstructs `(B_ext, A)` iff `B_col ⊑ B_ext`). Since `B₂ ⊑ B₁` would yield `⊥_B = B₁ ⊓ B₂ = B₂ ≠ ⊥_B` (contradiction), `B₂ ⋢ B₁`.
     - For (3), any node `(B_node, X)` in `π` with `B₂ ⋢ B_node` cannot become `obstructed` by any collision at or below `B₂`; by structural induction over the acyclic DAG `π`, every dependency in `π` remains in `Live(Σ₁)`, so `(B₁, ±Y [π]) ∈ Live(Σ₁)`.

5. `Exploratory` **MT-5: Meet-Stability of Cover-Witnessed Disjunction (`D2`) & Soundness of `∨E` Gluing** ([core.md](core.md) §2 item 5, §3 item 12; [`layer4-conjunction-disjunction-and-covers`](../docs/design-review.md#layer4-conjunction-disjunction-and-covers)):
   - **Statement**:
     1. **Downward Heredity of `D2` Disjunction**: If `Σ ; B ⊩⁺ (A ∨ C) [π]` is grounded by a witnessed exhaustive cover `{B₁, ..., B_k} ▷ B`, then for every non-empty sub-boundary `B' ⊑ B`, `{B_i ⊓ B' | B_i ⊓ B' ≠ ⊥_B} ▷ B'` witnesses `Σ ; B' ⊩⁺ (A ∨ C)`.
     2. **Soundness of Cover Gluing (`∨E`)**: From `Live` `B ⊩⁺ (A ∨ C)` (via `{B_i} ▷ B`), `Live` `B ⊩⁺ (A → E)`, and `Live` `B ⊩⁺ (C → E)`, every cell `B_i` acquires a `Live` witness `B_i ⊩⁺ E`, justifying `B ⊩⁺ E`.
   - **Proof Sketch**:
     - By Axiom 3 (Meet-Stability, [core.md](core.md) §2 item 5), `{B_i ⊓ B' | B_i ⊓ B' ≠ ⊥_B}` is a witnessed exhaustive cover of `B'`; by Axiom 5 (Non-Vacuity) and `B' ≠ ⊥_B`, this cover contains at least one non-empty cell `B_j ⊓ B'`. On each such cell `B_j ⊓ B' ⊑ B_j`, downward heredity (`§3 item 9`) inherits whichever of `B_j ⊩⁺ A` or `B_j ⊩⁺ C` held on `B_j`.
     - For `∨E`, downward heredity restricts both `B ⊩⁺ (A → E)` and `B ⊩⁺ (C → E)` to every cell `B_i ⊑ B`. Since each non-empty `B_i` has a `Live` witness for either `A` or `C`, `Scoped Cut` (`B_i ⊓ B_i = B_i ≠ ⊥_B`) produces `B_i ⊩⁺ E` on every cell of `{B_i} ▷ B`. Gluing across the exhaustive cover `{B_i} ▷ B` grounds `B ⊩⁺ E`.
   - **Standalone Gluing Boundary**: While [core.md](core.md) embeds sheaf/Beth gluing inside `∨I`, `∨E`, and cover-based `∀I`, neither [core.md](core.md) nor `src/engine.ts` yet exposes a general standalone **Sheaf Gluing** structural rule (`{B_i} ▷ B` and `∀i. B_i ⊩⁺ E [Live] ⟹ B ⊩⁺ E`) for arbitrary `E`.

---

## 4. Inquiry Dynamics & Anti-Immunization

6. `Exploratory` **MT-6: Polarity Purity of `Retract`, Reinstatement & Vertical Non-Commutativity** ([core.md](core.md) §2 item 7; [`layer4-negation-vs-exclusion`](../docs/design-review.md#layer4-negation-vs-exclusion)):
   - **Statement**:
     1. **Pure Cancellation (Sanskrit *prasajya-pratiṣedha*)**: Applying `Retract(g)` strictly deletes `g` from `G⁺ ∪ G⁻` without adding any element to either `G⁺` or `G⁻`. In particular, if `(B, A)` was `Grounded` (resp. `Excluded`) in `Σ` solely via a unique base leaf `g`, then in `Retract(g)(Σ)` the status of `(B, A)` becomes `Open`, never `Excluded` (resp. `Grounded`).
     2. **Quarantine Reinstatement**: If `(B, A)` was in `Collision` between `+A [g⁺]` and `-A [g⁻]`, then `Retract(g⁻)` removes the collision and restores `Live` authority to `+A [g⁺]` and any downstream derivations depending solely on `g⁺` and other `Live` leaves (without adding new positive leaves).
     3. **Vertical Non-Commutativity**: Vertical transition sequences `Σ₀ → Σ₁ → Σ₂` violate `Exchange` (`Observe⁺(B, A, w); Retract(w)` differs from `Retract(w); Observe⁺(B, A, w)`).
   - **Proof Sketch**: Immediate from the state transition definition (`§2 item 7`): `Retract(g)` modifies `Σ = (G⁺, G⁻, C_B, O_rev)` solely by set difference on `G⁺ ∪ G⁻` and re-evaluation of derived provenance. Since every derived entry for `±A` requires at least one base leaf in `G⁺ ∪ G⁻` (or structural `C_B`) by MT-1, deleting the sole base leaf eliminates all derived entries on that polarity without constructing an opposite-polarity leaf. Counterexample for (3): starting from `Open` `(B, A)` with `w ∉ G⁺`, `Observe⁺(B, A, w); Retract(w)` ends in `Open`, whereas `Retract(w); Observe⁺(B, A, w)` leaves `(B, A)` `Grounded`.

7. `Exploratory` **MT-7: `M1` + `M2` Anti-Immunization Guarantees & Proxy-Excision Boundary** ([core.md](core.md) §2 item 7; [worked-examples.md](worked-examples.md) §2; [`layer3-boundary-composition`](../docs/design-review.md#layer3-boundary-composition), [`layer5-content-and-coreference`](../docs/design-review.md#layer5-content-and-coreference)):
   - **Statement**: Let `Σ` contain counterexample `B ⊩⁻ A(w)` (`w ∈ Dom(B)` verified under `I_B`), putting `(B, ∀(x : B) A(x))` into `Excluded` or `Collision`. Then any transition `RefineBoundary(B → B' = B ⊓ [δ])` admitted by `M1 + M2` guarantees:
     1. **Non-Erasure (`M2`)**: `(B, ∀(x : B) A(x))` remains `Excluded` in every downstream state unless `w` itself is explicitly withdrawn via `Retract`.
     2. **Non-Circularity (`M1(i)`)**: `δ` introduces zero direct or indirect dependence on the target relation of `A`, eliminating tautological immunizations such as `δ(x) := A(x)`.
     3. **Non-Contingency Against Named Handles (`M1(ii)`)**: `δ` contains no contingent handle reference (`kind === "contingent"`), blocking bare extensional excision `δ(x) := ~(x ≈_B w)` while permitting structurally defined singularities (`AddId(x)` for `ℝ \ {0}`).
   - **Disguised Contingent Proxy Boundary (Open Tension)**: Syntactic handle-kind tagging (`structural` vs. `contingent` in `src/boundary.ts` / `src/engine.ts`) blocks explicit handle excision (`x ≉_B swan_402`), **but** does not automatically prevent an agent from conjoining multiple contingent empirical predicates (e.g., `~FoundInLake7(x) ∨ ~TaggedOnTuesday(x)`) that extensionally excise only `swan_402` without naming its identifier. Full semantic resistance to proxy immunization relies on requiring `δ` to carry independent cross-handle predictivity ([worked-examples.md](worked-examples.md) §2 Attempt 3) or explicit methodological review.

---

## 5. Four-Tier Specialization & Classical Recovery

8. `Exploratory` **MT-8: Soundness of `UL-Minimal` & Conservative `⊥ → C` Extension for `UL-Intuitionistic`** ([core.md](core.md) §4 item 13; [`layer2-classical-boundary-recovery`](../docs/design-review.md#layer2-classical-boundary-recovery)):
   - **Statement**:
     1. **`UL-Minimal` Specialization**: Under monotone `Σ` (forbidding `Retract`) and `No-Gluts` (zero collisions across `(B, X)`), every grounded derivation in `UL-Core` satisfies `Live(Σ)`, Quarantine never triggers, `Scoped Cut` equals unrestricted `Cut`, and the positive fragment over `{∧, ∨, →, ∀, ∃, ⊥, ~}` validates **Minimal Constructive Logic** augmented with Nelson-style strong negation `~A` (`(A → ⊥) → ⊥ ⊬ A` and `⊬ A ∨ ~A`).
     2. **Conservative `UL-Intuitionistic` Extension**: Adding the boundary axiom `B ⊩⁺ (⊥ → C)` for every item `C` preserves soundness (`No-Gluts`) and yields **Heyting Intuitionistic Beth-Cover Semantics** over finitary covers ([core.md](core.md) §2 item 5, §3 item 12).
   - **Proof Sketch**:
     - Under `No-Gluts`, `collisions = ∅`, so `obstructed_Σ(e)` is identically false; by MT-1, every well-founded entry in `Entries(Σ)` lies in `Live(Σ)`. Consequently `Scoped Cut` applies unconditionally across overlapping boundaries. Since `∨` requires a witnessed cover (`D2`) and structural impossibility (`A → ⊥`) induces only `-A` without double-negation elimination, neither `A ∨ ~A` nor `(A → ⊥) → ⊥ ⊢ A` is derivable on an `Open` item.
     - Under `UL-Intuitionistic`, `B ⊩⁻ ⊥` holds structurally for all `B ≠ ⊥_B` (`MT-3`), so `No-Gluts` implies no ground `B ⊩⁺ ⊥` exists on any non-empty `B`. Therefore Modus Ponens with `⊥ → C` can never fire to manufacture `B ⊩⁺ C` or create a new collision.
   - **Semantic vs. Syntactic Completeness Boundary**: MT-8 establishes **semantic soundness and Beth-cover validity**, treating `B ⊩⁺ (A → C)` and `B ⊩⁺ ∀(x : D) A(x)` semantically (as witness-preserving transformations / exhaustive domain checks). Full **proof-theoretic completeness** relative to natural-deduction Minimal/Intuitionistic FOL requires extending [core.md](core.md) §3 and `src/engine.ts` with explicit hypothetical sub-proof boxes (`→I` discharge) and open-domain eigenvariable `∀I`.

9. `Exploratory` **MT-9: `UL-Classical` Bivalent Recovery (`2` on Atomic `B*` and `2^k` on Atomic Covers)** ([core.md](core.md) §4 item 13; [worked-examples.md](worked-examples.md) §4; [`scope-anchor-unified-core`](../docs/design-review.md#scope-anchor-unified-core)):
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
   - **Reference Kernel Note**: In `src/specializations.ts`, `evaluateClassicalSpecialization` evaluates `evalOnAtomicCell` accurately per cell `B*_i`, so global tautologies (`A ∨ ~A`) return `polarity: "+"`. However, `ClassicalValuation` compresses the `2^k` cell vector onto a single `"+" | "-"` polarity (equating `"split across cells"` with `"globally excluded"`), which warrants distinguishing global-`+` / split / global-`-` in future multi-cell reporting.

---

## 6. Open Metatheoretic Tensions & Audit Summary

| ID | Finding | Affected Theorems | Spec / Kernel Impact |
| :--- | :--- | :--- | :--- |
| **G-1** | **Ghost Collision Under Eager Closure**: Dead raw entries generated prior to premise collision can collide with valid opposite-polarity grounds. | MT-1 | Require stratified / non-ghost collision checks in [core.md](core.md) §3 item 10 and `src/engine.ts`. |
| **G-2** | **Mutual Recursion in Strict Positivity**: Formation check handles single recursive definitions but does not walk mutual dependency cycles. | MT-2 | Extend cycle-polarity check in `src/syntax.ts` to arbitrary finite definition environments. |
| **G-3** | **`Observe⁺(B, ⊥)` & Unsourced `+(A → ⊥)` Tension**: Spec states `⊩⁺ ⊥` never holds, yet neither [core.md](core.md) nor `src/engine.ts` bars direct `Observe⁺(B, ⊥)` or unsourced `+(A → ⊥)`. | MT-3 | Either enforce admissibility guards + `+(A → ⊥) ⟹ -A`, or scope "`⊩⁺ ⊥` never holds" to `Live` grounds. |
| **G-4** | **Syntactic `→I` / Schematic `∀I` & Standalone Cover-Gluing**: Semantic recovery holds for `UL-Minimal` and `UL-Intuitionistic`, but syntactic sub-proof boxes and standalone `Cover-Gluing` are absent. | MT-5, MT-8 | Add explicit `→I` hypothetical sub-proofs, eigenvariable `∀I`, and standalone cover gluing as next kernel/spec milestone. |
| **G-5** | **Disguised Contingent Proxies & `2^k` Output Collapse**: Syntactic handle tags miss coincidental contingent predicate conjunctions (`M1(ii)`), and `src/specializations.ts` collapses `split` vs. `global -` on `2^k` covers. | MT-7, MT-9 | Strengthen `M1` definability documentation and report per-cell / split status in `ClassicalValuation`. |
