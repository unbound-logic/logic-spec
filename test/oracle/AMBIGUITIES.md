# Ambiguities in `Π(Σ)` met by the clean-room oracle

The oracle in [`pi-sigma.ts`](pi-sigma.ts) implements the evaluation program `Π(Σ)` of [`spec/core.md`](../../spec/core.md) §5 item 14 from the specification alone, without consulting the reference kernel. Where item 14 is ambiguous or underspecified, the oracle follows the reading closest to the text. Each entry below quotes the sentence relied on, states the reading chosen, and names the alternative, so the differential comparison with the kernel can separate oracle readings from kernel deviations.

The maintainer ruled on every reading after the differential comparison with the kernel (`audit-spec-kernel-coupling` in [`docs/design-review.md`](../../docs/design-review.md), revised 2026-11-26), and item 14 as amended in `main` commit `7b36043` ratifies them "as written there, except where this item now states otherwise". A3, A6 and A13 were amended by item 14: their original readings are kept below as superseded, followed by the amended reading the oracle now follows. Every other entry is ratified as recorded; its status line notes where item 14 now states the reading itself. Each entry is `[Decided]` (AGENTS.md §2 item 5). The code cites these entries as `A1` … `A21`.

## Universe

**A1. `⊤_B` belongs to `𝔅(Σ)`.** `[Decided]`
- Status: ratified; item 14 now states that `𝔅(Σ)` includes `⊤_B`.
- Text: "`𝔅(Σ)` is the set of non-empty boundaries declared in `Σ`".
- Ambiguity: `⊤_B` is present in every boundary system without being declared by an inquiry transition.
- Reading: `𝔅(Σ)` is `BoundarySystem.nonEmptyBoundaries()`, which includes `⊤_B`, because item 4 makes `⊤_B` part of every bounded semilattice. Consequences: `⊤_B` gets rows, the structural `(⊤_B, -, ⊥)`, and `obs(⊤_B, A)` whenever any boundary collides on `A`.
- Alternative: only user-declared boundaries; `⊤_B` would then never hold a record.

**A2. Items tracked by `Σ`.** `[Decided]`
- Status: ratified; item 14 now defines the tracked items this way, adding the items of recorded theorems, which the oracle's state description does not carry (A15).
- Text: "`U(Σ, Q)` is the set of items tracked by `Σ` and the items of `Q`".
- Ambiguity: "tracked" is not defined.
- Reading: the item of every observation, both sides of every incompatibility `A ⊥_B C`, and for every structural collapse `B ⊓ [A] = ⊥_B` both `A` and `A → ⊥`, since the Structural row concludes `(B, +, A → ⊥)` and a conclusion outside `U(Σ, Q)` has no atom.
- Alternative: a collapse tracks only `A`; then `A → ⊥` is evaluated only when queried.

**A3. Polarity flips in `U(Σ, Q)`.** `[Decided]`
- Status: amended by item 14.
- Text (before `7b36043`): "A polarity flip `~A` belongs to `U(Σ, Q)` only when it is tracked or queried."
- Ambiguity: whether a flip nested inside a tracked or queried item (or produced as a quantifier instance or a sub-item of another flip) counts as tracked or queried.
- Original reading (superseded): literal. The restriction applies to the closure as a whole, so a flip that arises only by closure is outside `U(Σ, Q)`. Consequences: querying `Q ∧ ~P` alone gives the conjunction no `+~P` premise; `∀(x : D) ~P(x)` has no instances `~P(w)`, so `∀E`, `∀` counterexample and `∀` generic cannot fire for it, and the duality `+∀x A ⟺ -∃x ~A` named in `audit-universal-existential-import` needs the flipped instances to be tracked or queried; a tracked `~~P` has no sub-item `~P`.
- Amended reading (item 14): "A polarity flip belongs to `U(Σ, Q)` exactly when it arises in this way; `U(Σ, Q)` is not closed under prefixing `~` to its members." A flip arising as a tracked or queried item, a direct sub-item, a quantifier instance or a congruence rewrite belongs to `U(Σ, Q)`, but no flip is ever added by prefixing `~` to a member. Tested in `test_oracle_nested_polarity_flips_belong_to_universe`.

**A4. Direct sub-items of quantifiers, reflections and references.** `[Decided]`
- Status: ratified; item 14 now states that a quantifier contributes its instances, not its open body.
- Text: "closed under direct sub-items, under quantifier instances `A(w)` and `δ(w)` for `w ∈ Dom(D)`".
- Reading: a quantifier contributes only its instances; the open body `A(x)` and constraint `δ(x)` are not items. A reflection `Refl_k(J)` and a named reference have no direct sub-items, since a reflection is about a judgment, not an item.
- Alternative: the open body counts as a sub-item; it would add rows that no rule ever fills unless observed.

**A5. Congruence rewrites in the universe are position-wise and cover `≈` items.** `[Decided]`
- Status: ratified; item 14 now defines the universe's congruence rewrites this way. Its Congruence row no longer writes `R[u/t]` (see A6).
- Text: "closed … under congruence rewrites of atoms by the handles of the boundaries in `𝔅(Σ)`".
- Ambiguity: item 14 does not define a congruence rewrite. Item 6 states it position-wise (`R(..., r: t₁, ...)` to `R(..., r: t₂, ...)`), while the Congruence row writes `R[u/t]`. "Atoms" may or may not include the reserved atomic form `t ≈_B u` of item 1.
- Reading: for every relational atom and every `≈` item in `U(Σ, Q)`, replace the handle at any one position by any handle of `Dom(B)` for any `B ∈ 𝔅(Σ)`, iterated to closure. This contains every chain of `R[u/t]` rewrites by such handles and the conclusions of `≈` symmetry and transitivity, which the all-occurrence rewrite alone would miss when no spare handle exists (from `a ≈_D b` with handles `{a, b}`, `b ≈_D a` is reachable only position-wise). Handles that belong to no boundary of `𝔅(Σ)` are never substituted in.
- Alternative: all-occurrence `R[u/t]` rewrites only, and relational atoms only; `≈` symmetry would then often have no conclusion atom.

## Rules

**A6. The Congruence rule's rewrite.** `[Decided]`
- Status: amended by item 14.
- Text (before `7b36043`): the Congruence row concludes `(B, p, R[u/t])`.
- Original reading (superseded): the standard substitution notation, so every occurrence of `t` in `R` becomes `u` (from `R(a, a)` and `a ≈ b`, only `R(b, b)`, not `R(a, b)`). Item 6 states the rewrite at a single position, but item 14 governs where they disagree.
- Amended reading (item 14): the Congruence row concludes "`(B, p, R')`, where `R'` replaces one occurrence of `t` in `R` by `u`", for `R` a relational atom, as item 6 states. From `R(a, a)` and `a ≈_D b` it concludes `R(a, b)` and `R(b, a)`, and `R(b, b)` in a second step. Tested in `test_oracle_congruence_rewrites_one_occurrence_at_a_time`.

**A7. Congruence applies to relational atoms only.** `[Decided]`
- Status: ratified; item 14's Congruence row now reads "`R` a relational atom of a relation native to `D`".
- Text: "`R` an atom of a relation native to `D`, `B ⊑ D`".
- Reading: `R` is a relational atom `R(r₁: t₁, ...)` whose relation satisfies `hasNativeRelation(D, R)`, where `D` is the subscript of the `≈` premise; `≈` items are rewritten only through symmetry and transitivity. Instances where `t` does not occur in `R` are omitted, since they conclude `R` itself.

**A8. A structural collapse fires on its registered boundary only.** `[Decided]`
- Status: ratified; item 14's Structural row now reads "on that `B` only (sub-boundaries receive it by heredity)".
- Text: the Structural row's side condition "`B ⊓ [A] = ⊥_B` in `C_B`".
- Reading: only the boundary `B` named by the registered constraint; sub-boundaries `B' ⊑ B` receive the records through downward heredity, whose `Live` status then also depends on `B` being unobstructed.
- Alternative: the collapse also holds as a structural ground on every `B' ⊑ B`, since `B' ⊓ [A] ⊑ B ⊓ [A] = ⊥_B`.

**A9. Structural reflexivity is `t ≈_B t` on its own boundary.** `[Decided]`
- Status: ratified.
- Text: Structural conclusion "`(B, +, t ≈_B t)`" with side condition "`t ∈ Dom(B)`".
- Reading: the conclusion's evaluation boundary equals the subscript of `≈`, membership is `isAdmissibleHandle(B, t)`, and the instance exists only when `t ≈_B t` belongs to `U(Σ, Q)`. On other boundaries, `t ≈_B t` holds only through heredity from `B`.

**A10. Witnessed covers.** `[Decided]`
- Status: ratified.
- Text: "a 'witnessed' cover is one that stays valid under `audit-cover-non-vacuity-drift`" and "Until those are specified, the registered covers and computed meets of item 4 and item 5 stand in for them"; `∨` by cover has no exclusion of `{B}`, while Cover-Gluing says "other than `{B}`".
- Reading: the witnessed covers of `B` are `BoundarySystem.witnessedCoversOf(B)`, the registered covers closed under the item 5 axioms, which includes the identity cover. `∨` by cover uses every one of them, so the identity cover gives `∨I` from a `Live` disjunct; Cover-Gluing skips only the cover whose sole cell is `B`, so a cover such as `{B, B₁}` still takes part.
- Limitation: `witnessedCoversOf` stops expanding covers above 16 cells; the oracle cannot detect that truncation and so cannot report non-convergence for it, as item 14's Role asks.

**A11. Known overlaps are computed meets.** `[Decided]`
- Status: ratified; item 14's Role now makes an ambiguous meet an error.
- Text: "`B₁ ⊓ B₂ ≠ ⊥_B` means an overlap that is known under `audit-unregistered-meet-closed-world`", with computed meets standing in until then.
- Reading: Scoped Cut uses `BoundarySystem.meet`, including its current reading of "no registered common sub-boundary" as disjointness. When `meet` reports an ambiguous meet, the oracle throws instead of guessing a conclusion boundary.

**A12. Which handles "`δ` excludes" in the `∃` exclusion.** `[Decided]`
- Status: ratified; item 14 now states "one instance per split of `Dom(D)` into an excluded part and the rest".
- Text: record premises "`(B, -, A(w))` for every `w ∈ Dom(D)` not excluded by `δ`", `Live` premises "`(B, -, δ(w))` for the handles `δ` excludes".
- Ambiguity: "excluded by `δ`" could be a fact of the model, which would need negation (`not live(B, -, δ(w))`) where item 14 allows negation only through `obs`.
- Reading: one rule instance per partition of `Dom(D)`, so each handle supplies either a `Live` `(B, -, δ(w))` or a record `(B, -, A(w))`, matching G2 ("for each handle, `Live -δ` or an exclusion record of the body"). Taking the partition determined by the model gives the same records. Without a constraint, every handle supplies `(B, -, A(w))`.

**A13. `∀` generic without a constraint, and empty or bottom domains.** `[Decided]`
- Status: amended by item 14.
- Text (before `7b36043`): `Live` premises "for every `w ∈ Dom(D)`: `(B, -, δ(w))`, or `(B, +, A(w))` with `(B, +, δ(w))` if constrained", side condition "`CloseDomain(D)` in `C_B`".
- Original reading (superseded in its last sentence): without a constraint the alternative `(B, -, δ(w))` does not exist, so every handle needs a `Live` `(B, +, A(w))`; with a constraint, each handle needs a `Live` `(B, -, δ(w))` or both a `Live` `(B, +, A(w))` and a `Live` `(B, +, δ(w))`. On a closed empty `Dom(D)` the rule fires with no premises (vacuous truth grounded by the closure alone), and likewise the `∃` exclusion. Item 14 sets no condition `D ≠ ⊥_B`, which `audit-universal-existential-import` states for vacuous truth, so a closure listed for `⊥_B` also yields vacuous results.
- Amended reading (item 14): `∀` generic and the `∃` exclusion require "`CloseDomain(D)` in `C_B`, `D ≠ ⊥_B`", and the alternative `(B, -, δ(w))` is marked "(constrained only)". A closure listed for `⊥_B` therefore grounds nothing, while a closed empty `Dom(D)` of a boundary `D ≠ ⊥_B` still yields vacuous truth grounded by the closure alone. Tested in `test_oracle_vacuous_grounding_requires_non_bottom_domain`.

**A14. Closures are taken as currently valid.** `[Decided]`
- Status: ratified.
- Text: "`CloseDomain(D)` is the closure of `audit-universal-existential-import`".
- Reading: the oracle receives the set of domains whose closure is witnessed and treats each as valid for the current `Dom(D)`. The anchoring rule of that decision (a closure becomes invalid when `Dom(D)` changes) concerns state transitions, which the oracle does not model. A closure applies only to the exact domain named, never to sub-boundaries `D' ⊑ D`, matching rule (2) of the decision.

**A15. Theorem and reflection values are not implemented.** `[Decided]`
- Status: ratified.
- Text: the Theorem row and the Structural conclusion "a reflection value" (item 3).
- Reading: left out by the oracle's brief. No theorem ever fires, and reflection items receive no structural value; they take part only in the rules that apply to every item.

**A16. Invalid states are rejected, not evaluated.** `[Decided]`
- Status: ratified.
- Text: item 12, "base observations obey `⊥ ∉ G⁺`"; item 7, observations are anchored "on non-empty `B ≠ ⊥_B`".
- Reading: the oracle throws on `+⊥` in the observations and on observations, incompatibilities, collapses, closures, `≈` subscripts or quantifier domains naming a boundary the system does not declare.

**A17. Atoms exist only for items of `U(Σ, Q)`.** `[Decided]`
- Status: ratified. Since A3 was amended, every flip a rule needs belongs to `U(Σ, Q)`, so this now affects only rewrites by handles outside `𝔅(Σ)`.
- Text: "Atoms: for `B ∈ 𝔅(Σ)`, `A ∈ U(Σ, Q)` and `p ∈ {+, -}`".
- Reading: a rule instance whose conclusion lies outside `U(Σ, Q)` does not exist, and a premise outside `U(Σ, Q)` never holds, so an alternative containing it is dropped. Under A5 this affects only flips (A3) and rewrites by handles outside `𝔅(Σ)`.

**A18. Obstruction includes the boundary itself.** `[Decided]`
- Status: ratified; item 14 now states that `⊑` is reflexive.
- Text: "`obs(B, A) ← coll(B', A)` for every `B' ∈ 𝔅(Σ)` with `B' ⊑ B`".
- Reading: `⊑` is reflexive (item 4), so a collision on `B` obstructs `B`, and each `obs` rule is a separate clause (one colliding sub-boundary suffices).

**A19. Incompatibility on every sub-boundary, in both directions.** `[Decided]`
- Status: ratified.
- Text: Incompatibility row, side condition "`A ⊥_B C` in `C_B`, `B' ⊑ B`".
- Reading: for every `B' ∈ 𝔅(Σ)` with `B' ⊑ B`, including `B`, two instances: `Live` `(B', +, A)` gives `(B', -, C)`, and `Live` `(B', +, C)` gives `(B', -, A)`.

**A20. The range of `E` in `∨E`.** `[Decided]`
- Status: ratified.
- Text: `∨E` concludes `(B, +, E)` from `Live` `(B, +, A ∨ C)`, `(B, +, A → E)`, `(B, +, C → E)`.
- Reading: one instance for every disjunction `A ∨ C` and every `E` such that both `A → E` and `C → E` belong to `U(Σ, Q)`.

## Reporting

**A21. Authority of absent records and the two `Collision` readings.** `[Decided]`
- Status: ratified for absent records. The Reporting section was then revised by G4b: a record is present only when its `rec` atom is true, `(B, A)` is in `Collision` exactly when `coll(B, A)` is true or undefined, and otherwise its status follows its present records; an absent record, now one whose `rec` atom is false or undefined, has no authority. The coincidence stated below therefore holds between `coll` and the `rec` atoms being true or undefined, no longer between `coll` and present records; a symmetric conflict now reads `Collision` with its undefined record absent. Tested in `test_oracle_symmetric_incompatibility_conflict` and `test_oracle_undefined_record_is_possible_but_not_present`.
- Text: "The authority of a present record is …" and "`(B, A)` is in `Collision` when `coll(B, A)` is true or undefined".
- Reading: an absent record (its `rec` atom false) has no authority, reported as `null`. The local status `Collision` (both records present) and the `coll` reading coincide, because `coll(B, A)` is true or undefined exactly when both `rec` atoms are; every such slot carries `Rev(B, A)`.
