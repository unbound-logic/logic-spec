---
title: UL-Core Worked Derivations & Adversarial Stress-Tests
version: 0.2.0
status: active
date: 2026-11-25
---

# Worked Derivations & Adversarial Stress-Tests (`UL-Core`)

This document exercises [spec/core.md](core.md) end to end on four benchmark scenarios: (1) multi-regime boiling-point collision, quarantine propagation, and `M2` refinement; (2) `M1` structural anti-immunization contrasting `ℝ \ {0}` against contingent swan excision; (3) four adversarial Curry Paradox attempts; and (4) `UL-Classical` recovery of LEM, safe material implication, and Modus Tollens.

---

## 1. Multi-Regime Collision, Quarantine & `M2` Non-Erasure

1. `Tested` **WE-1: Boiling Point Under `1 atm` vs. `2 atm`** ([`core.md`](core.md) §2 items 4, 7; §3 items 8–12):
   - **Signature & Boundaries**:
     - `B_1atm ⊑ B_all`, `B_2atm ⊑ B_all`, with `B_1atm ⊓ B_2atm = ⊥_B` (disjoint regimes).
     - Items: regime-scoped `Heat100 := Heat100(substance: h2o)`, `Boils := Boils(substance: h2o)`, `Cook := CooksAt100C(item: pasta)`, `Rule_broad := Heat100 → Boils`, `Rule_cook := Boils → Cook`; paired with parameter-indexed schema `HeatedAt(p) := HeatedAt(pressure: p)`, `BoilsAt(p) := BoilsAt(pressure: p)`, and `Gen_all := ∀(p : B_all) (HeatedAt(p) → BoilsAt(p))`.
   - **Stage `Σ₀` (Initial Grounding)**:
     ```text
     Observe⁺(B_all,  Rule_broad, w₁)
     Observe⁺(B_all,  Rule_cook,  w₂)
     Observe⁺(B_1atm, Heat100,    w₃)
     Observe⁺(B_1atm, Boils,      w_emp)   // independent local observation at 1 atm
     Observe⁺(B_all,  Gen_all,    w₄)
     ```
     - By downward heredity (§3 item 9) and Scoped Cut (§3 item 11), `B_1atm ⊩⁺ Boils` has two independent `Live` provenance DAGs:
       - `π₁ = MP(w₃, Down(B_all→B_1atm, w₁))` (depends on overbroad `w₁`)
       - `π₂ = w_emp` (independent local witness)
     - Likewise `B_1atm ⊩⁺ Cook` has both `MP(π₁, Down(w₂))` and `MP(π₂, Down(w₂))`.
   - **Stage `Σ₁` (Counterexample Arrives at `2 atm`)**:
     ```text
     Observe⁺(B_2atm, Heat100,        w₅)
     Observe⁻(B_2atm, Boils,          w₆)      // localized refutation of Rule_broad under 2 atm regime
     Observe⁺(B_all,  HeatedAt(2atm), w₅_all)
     Observe⁻(B_all,  BoilsAt(2atm),  w₆_all)  // water at 2 atm does not boil at 100C
     ```
     - By §3 item 12 (`-(A → C)`), derive `B_2atm ⊩⁻ Rule_broad [Counter(w₅, w₆)]`.
     - By symmetric downward heredity (§3 item 9), `w₁` inherits down to `B_2atm ⊩⁺ Rule_broad [Down(B_all→B_2atm, w₁)]` → **`(B_2atm, Rule_broad)` enters `Collision`** and records `Rev(B_2atm, Rule_broad) ∈ O_rev`.
     - **Zero Leakage Check**: Because `B_1atm ⊓ B_2atm = ⊥_B`, `B_2atm ⊩⁻ Rule_broad` **never** propagates to `B_1atm`.
     - **Upstream Obstruction & Selective Quarantine (§3 item 10)**:
       - `(B_all, +Rule_broad [w₁])` is obstructed by sub-boundary collision at `B_2atm` and loses `Live` authority immediately.
       - Therefore `π₁ = MP(w₃, Down(B_all→B_1atm, w₁))` loses `Live` authority (you may no longer rely on the falsified universal law at `1 atm`).
       - However, `π₂ = w_emp` and `MP(π₂, Down(w₂))` contain no un-`Live` nodes, so `B_1atm ⊩⁺ Boils [w_emp]` and `B_1atm ⊩⁺ Cook [MP(π₂, Down(w₂))]` **remain `Live`** without global Explosion.
     - Simultaneously, `w = 2atm ∈ Dom(B_all)` with `w₅_all` and `w₆_all` yields `B_all ⊩⁻ (HeatedAt(2atm) → BoilsAt(2atm))`, hence `B_all ⊩⁻ Gen_all` by §3 item 12, colliding with `w₄` and recording `Rev(B_all, Gen_all) ∈ O_rev`.
   - **Stage `Σ₂` (Discharge via `Retract` + `RefineBoundary` Obeying `M1` & `M2`)**:
     ```text
     Retract(w₁)
     Retract(w₄)
     Observe⁻(B_all, Pressure(2atm, 1atm), w_p2)   // separating evidence for M1(iv)
     RefineBoundary(B_all → B_1atm = B_all ⊓ [Pressure(p, 1atm)])
     Observe⁺(B_1atm, Rule_broad, w₁')
     Observe⁺(B_1atm, ∀(p : B_1atm) (HeatedAt(p) → BoilsAt(p)), w₄')
     ```
     - **M1 Check**: `δ(p) := Pressure(p, 1atm)` is non-circular (does not mention `BoilsAt`) and structurally definable (physical regime parameter); by domain binding (M1(iv)) the excised handle `2atm` carries `Live -Pressure(2atm, 1atm)` from `w_p2`, while `1atm` is kept. Admissible.
     - **M2 Check**: `(B_all, Gen_all)` stays recorded as **`Excluded (-)`** (never erased), while `∀(p : B_1atm) (HeatedAt(p) → BoilsAt(p))` is **`Grounded (+)`** with explicit narrowing provenance, discharging `O_rev`.
   <!-- @assert-count target="test/calculus-and-quarantine.test.ts" symbol="function test_quarantine_upstream_obstruction_and_selective_survival" min="1" reason="Boiling-point multi-regime collision, selective quarantine, and M2 non-erasure are verified" -->

---

## 2. `M1` Anti-Immunization & Anti-Equivocation (`ℝ \ {0}` vs. Swan `#402`)

2. `Tested` **WE-2: Admissible Algebraic Singularity (`ℝ \ {0}`) vs. Refused Contingent Excision (`swan_402`)** ([`core.md`](core.md) §2 items 6–7):
   - **Case 2A — Admissible Refinement (`ℝ \ {0}`)**:
     - Boundary `ℝ` carries field operations `+, ×` and the structurally defined relation `AddId(x) := ∀(y : ℝ) (y + x ≈_ℝ y)`.
     - Claim: `Gen_ℝ := ∀(x : ℝ) Invertible(x)` where `Invertible(x) := ∃(y : ℝ) (x × y ≈_ℝ 1)`.
     - Counterexample: `0 ∈ Dom(ℝ)` satisfies `ℝ ⊩⁻ Invertible(0)`, yielding `ℝ ⊩⁻ Gen_ℝ`.
     - Proposed refinement `RefineBoundary(ℝ → ℝ* = ℝ ⊓ [~AddId(x)])`:
       - **M1(i) Non-Circularity**: `~AddId(x)` does not reference `Invertible(x)` → **Pass**.
       - **M1(ii) Structural Definability**: `AddId(x)` is defined by `ℝ`'s algebraic structure rather than a contingent handle tag → **Pass**.
       - **M1(iv) Domain Binding**: `Observe⁺(ℝ, AddId(0))` gives `Live -~AddId(0)`, so the excised `0` fails `δ`, while `2` keeps an `Open` `δ` and stays in `ℝ*` → **Pass**.
       - **M2 Non-Erasure**: `(ℝ, Gen_ℝ)` remains `Excluded (-)`, while `(ℝ*, ∀(x : ℝ*) Invertible(x))` is `Grounded (+)`.
   - **Case 2B — Refused Ad-Hoc Immunizing Stratagems (`swan_402`)**:
     - Boundary `Swan`, claim `Gen_Swan := ∀(x : Swan) White(x)`, refuted by `Observe⁻(Swan, White(swan_402), obs_tue)` with `I_Swan(swan_402)` verified.
     - Attempt 1: `δ₁(x) := White(x)` → **Refused by M1(i)** (circular reference to `White`).
     - Attempt 2: `δ₂(x) := ~(x ≈_Swan swan_402)` → **Refused by M1(ii)** (bare excision of contingent empirical handle `swan_402`).
     - Attempt 2b (Disguised Contingent Proxy): `δ_proxy(x) := ~(FoundInLake7(x) ∧ TaggedOnTuesday(x))` → **Refused by M1(iii)** (no independent `Live +δ` witness on a non-refuted surviving handle such as `swan_101`, blocking disguised proxy, `-δ` pseudo-witnesses, or vacuous sub-boundary excision; see [metatheory.md](metatheory.md) `MT-7` for the Honest-Proxy Symbol-Isomorphism Horizon).
     - Attempt 2c (Decorative Criterion): `δ_dec(x) := Feathered(x)` with `Feathered(swan_402)` and `Feathered(swan_101)` both observed → **Refused by M1(iv)** (the excised counterexample satisfies `δ_dec`, so `δ_dec` separates nothing).
     - Attempt 3 (Admissible): `δ₃(x) := ~Habitat(x, Australia)` backed by independent `Live +δ₃` witness `obs_eu_habitat` on `swan_101` (with no surviving handle witnessing `-δ₃`) and by separating evidence `Observe⁺(Swan, Habitat(swan_402, Australia))`, which gives `Live -δ₃(swan_402)` (M1(iv)) → **Admitted by M1** (non-circular, independently testable across fresh handles `u ≉_Swan swan_402`), while **M2** preserves `(Swan, Gen_Swan)` as `Excluded (-)`.
   - **Case 2C — Anti-Equivocation Guard (§2 item 6)**:
     - An observation `Observe⁻(Swan, White(bird_99), obs_wed)` where `bird_99` fails `I_Swan` (e.g., a painted goose) cannot witness `bird_99 ∈ Dom(Swan)` and therefore **cannot** collide with `Gen_Swan`.
   <!-- @assert-count target="test/boundary-and-inquiry.test.ts" symbol="function test_inquiry_updates_retract_non_commutativity_and_m1_m2" min="1" reason="R \\ {0} and swan #402 M1/M2 scenarios are verified" -->
   <!-- @assert-count target="test/boundary-and-inquiry.test.ts" symbol="function test_m1_iii_excess_content_blocks_disguised_proxies_and_preserves_structural_singularities" min="1" reason="M1(iii) disguised proxy refusal, vacuous/collided witness rejection, and structural singularity preservation are verified" -->
   <!-- @assert-count target="test/boundary-and-inquiry.test.ts" symbol="function test_coreference_multi_granularity_and_anti_equivocation" min="1" reason="Anti-equivocation guard for bird_99 is verified" -->
   <!-- @assert-count target="test/boundary-and-inquiry.test.ts" symbol="function test_m1_binding_rejects_criteria_not_shown_to_exclude_excised_handles" min="1" reason="M1 domain binding refuses decorative and untested criteria and kept excluded handles" -->

---

## 3. Adversarial Curry Paradox Attempts (All Blocked)

3. `Tested` **WE-3: Four Curry Attack Vectors Against Horizontal Contraction** ([`core.md`](core.md) §1 items 2–3; §3 items 11–12):
   - Target arbitrary noise: `Z := MoonIsCheese`.
   - **Vector 1 — Direct Negative Recursion (`K := K → Z`)**:
     - `K` occurs to the left of `→` (non-strictly-positive). **Rejected at formation time by §1 item 3 (Strict Positivity).**
   - **Vector 2 — Same-Level Reflection Diagonal (`K_n := Refl_k(Σ ; B ⊩⁺ K_n) → Z`)**:
     - §1 item 3 (Level Stratification) requires `k < n` where `k = level(K_n) = n`, yielding `n < n` (impossible). **Rejected at formation time.**
     - Attempting a valid cross-stage variant `K_{t+1} := Refl_t(Σ_t ; B ⊩⁺ K_t) → Z` is well-formed, but assuming `K_t` does **not** unfold into `K_{t+1}`, breaking Step 2 (`K ⊢ K → Z`) of the 7-step Curry derivation.
   - **Vector 3 — Polarity-Flip Disguise (`K := (~K) → Z`)**:
     - `K` appears inside an unguarded `~` feeding the antecedent of `→`. **Rejected at formation time by §1 item 3.**
   - **Vector 4 — Boundary-Promotion Disguise (`K := ∀(y : B ⊓ [K]) Z`)**:
     - Promoting `K` into the contravariant boundary constraint `[K]` / universal domain `D` acts equivalently to a conditional antecedent `K → Z`. **Rejected at formation time by §1 item 3 (Strict Positivity covers contravariant boundary/domain positions).**
   <!-- @assert-count target="test/syntax-and-curry.test.ts" symbol="function test_curry_firewall_blocks_all_four_vectors_and_allows_cross_stage" min="1" reason="All four adversarial Curry attack vectors and valid cross-stage reflection are verified" -->
   <!-- @assert-count target="test/reflection.test.ts" symbol="function test_cross_stage_reflection_curry_immunity_and_deduction_stratification" min="1" reason="Operational Vector 2 cross-stage reflection Curry immunity is verified" -->

---

## 4. `UL-Classical` Step-by-Step Boundary Recovery

4. `Tested` **WE-4: Derived Classical Theorems Under Closure Conditions** ([`core.md`](core.md) §4 item 13):
   - Assume `UL-Classical`: frozen `Σ`, atomic closed boundary `B* ≠ ⊥_B` (or witnessed finite atomic cover `{B*_1, ..., B*_k} ▷ B`), finest congruence `≈_{B*}`, `No-Gluts`, `No-Gaps`, and level `n = 0`.
   - **Derivation 4A — Non-Atomic Excluded Middle (`B ⊩⁺ (A ∨ ~A)`)**:
     1. For each atomic cell `B*_i` in `{B*_i} ▷ B`, `No-Gaps` yields either `B*_i ⊩⁺ A` or `B*_i ⊩⁻ A`.
     2. Whenever `B*_i ⊩⁻ A`, §3 item 12 (`~`) yields `B*_i ⊩⁺ (~A)`.
     3. By `No-Gluts`, every per-cell ground is `Live`.
     4. By §3 item 12 (Cover-Witnessed Disjunction `D2`), `{B*_i} ▷ B` witnesses `B ⊩⁺ (A ∨ ~A)`.
   - **Derivation 4B — Material Implication Closure Without Modus Ponens Leakage**:
     1. Suppose atomic-generated `B*` has `B* ⊩⁻ A` and `B* ⊩⁻ C` (in `UL-Core`, `A → C` remains `Open`).
     2. By `No-Gluts`, `B* ⊩⁺ A` fails; hence under `UL-Classical` closure over atomic/congruence grounds, neither `+A ∧ -C` nor any exclusion `B* ⊩⁻ (A → C)` holds.
     3. By `No-Gaps`, `B* ⊩⁺ (A → C)` holds (recovering classical `False → False` = True).
     4. Because `B* ⊩⁺ A` does not hold (`No-Gluts`), Scoped Cut / Modus Ponens (§3 item 11) **cannot** fire to derive `+C`.
   - **Derivation 4C — Classical Modus Tollens (`+(A → C)` and `+(~C)` ⇒ `+(~A)`)**:
     1. Given `B* ⊩⁺ (A → C)` and `B* ⊩⁺ (~C)` (hence `B* ⊩⁻ C` by §3 item 12).
     2. If `B* ⊩⁺ A` held, Scoped Cut (§3 item 11) would derive `B* ⊩⁺ C`, colliding with `B* ⊩⁻ C` and violating `No-Gluts`.
     3. Hence `B* ⊩⁺ A` fails; by `No-Gaps`, `B* ⊩⁻ A` must hold, yielding `B* ⊩⁺ (~A)` by §3 item 12.
   <!-- @assert-count target="test/specializations.test.ts" symbol="function test_four_tier_deductive_spectrum_and_classical_recovery" min="1" reason="Derivations 4A, 4B, and 4C for UL-Classical recovery are verified" -->
