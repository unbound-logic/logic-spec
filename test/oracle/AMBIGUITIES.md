# Ambiguities in `Π(Σ)` met by the clean-room oracle

The oracle in [`pi-sigma.ts`](pi-sigma.ts) implements the evaluation program `Π(Σ)` of [`spec/core.md`](../../spec/core.md) §5 item 14 from the specification alone, without consulting the reference kernel. Where item 14 is ambiguous or underspecified, the oracle follows the reading closest to the text. Each entry below quotes the sentence relied on, states the reading chosen, and names the alternative, so the differential comparison with the kernel can separate oracle readings from kernel deviations.

The maintainer ruled on every reading after the differential comparison with the kernel (`audit-spec-kernel-coupling` in [`docs/design-review.md`](../../docs/design-review.md), revised 2026-11-26), and item 14 as amended in `main` commit `7b36043` ratifies them "as written there, except where this item now states otherwise". A3, A6 and A13 were amended by item 14: their original readings are kept below as superseded, followed by the amended reading the oracle now follows. Every other entry is ratified as recorded; its status line notes where item 14 now states the reading itself. Each of `A1` … `A21` is `[Decided]` (AGENTS.md §2 item 5). Entries `A22` … `A25` record the oracle's readings of item 14 as amended in `main` commit `9c0fd4d`, and entries `A26` … `A32` its readings of items 4 and 14 as amended in `main` commit `5a385ce`, which make overlap three-valued (`audit-unregistered-meet-closed-world`); they stay `[Exploratory]` until the maintainer rules on them. Item 4 as amended in `5a385ce` supersedes A11's closed-world reading. The code cites these entries as `A1` … `A32`.

## Universe

**A1. `⊤_B` belongs to `𝔅(Σ)`.** `[Decided]`
- Status: ratified; item 14 now states that `𝔅(Σ)` includes `⊤_B`.
- Text: "`𝔅(Σ)` is the set of non-empty boundaries declared in `Σ`".
- Ambiguity: `⊤_B` is present in every boundary system without being declared by an inquiry transition.
- Reading: `𝔅(Σ)` is `BoundarySystem.nonEmptyBoundaries()`, which includes `⊤_B`, because item 4 makes `⊤_B` part of every bounded semilattice. Consequences: `⊤_B` gets rows, the structural `(⊤_B, -, ⊥)`, and `obs(⊤_B, A)` whenever any boundary collides on `A`.
- Alternative: only user-declared boundaries; `⊤_B` would then never hold a record.

**A2. Items tracked by `Σ`.** `[Decided]`
- Status: ratified; item 14 now defines the tracked items this way, adding the items of recorded theorems, which the oracle's state description does not carry (A15). Since `9c0fd4d`, item 14 also tracks `⊥` (A22) and the items of past transitions (A23).
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
- Limitation: `witnessedCoversOf` stops expanding covers above 16 cells; the oracle cannot detect that truncation and so cannot report non-convergence for it, as item 14's Role asks. Its Meet-Stability pullbacks across an unknown overlap are A32.

**A11. Known overlaps are computed meets.** `[Decided]`
- Status: superseded by item 4 as amended in `5a385ce`, which makes overlap three-valued; the oracle now follows A26 and A27. The last sentence of the original reading (an ambiguous meet is an error) still holds, as item 14's Role states; A31 records where the oracle raises it.
- Text (before `5a385ce`): "`B₁ ⊓ B₂ ≠ ⊥_B` means an overlap that is known under `audit-unregistered-meet-closed-world`", with computed meets standing in until then.
- Original reading (superseded): Scoped Cut uses `BoundarySystem.meet`, including its current reading of "no registered common sub-boundary" as disjointness. When `meet` reports an ambiguous meet, the oracle throws instead of guessing a conclusion boundary.
- Amended reading (item 4 and item 14): Scoped Cut fires only when "`B₁` and `B₂` [are] known to overlap (item 4)", at their meet; an unknown overlap "licenses no Scoped Cut", like a disjoint one. The oracle reads the three cases from `BoundarySystem.meetStatus` (A26) and never calls `meet`. Tested in `test_oracle_scoped_cut_needs_known_overlap`.

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

## Readings of item 14 as amended in `9c0fd4d`

**A22. `⊥` is a tracked root in every state.** `[Exploratory]`
- Text: "The items **tracked** by `Σ` are `⊥` and every item named by a transition in the history of `Σ`".
- Reading: the oracle adds `⊥` to the tracked items of every state, so `U(Σ, Q)` always contains `⊥` and the Structural row gives `(B, -, ⊥)` on every `B ∈ 𝔅(Σ)`, `⊤_B` included (A1). A state with no observations has the universe `{⊥}`. `⊥` has no sub-items and no congruence rewrites, so it adds nothing else. Tested in `test_oracle_bottom_is_always_tracked`.

**A23. Items of past transitions are passed as `historyItems`.** `[Exploratory]`
- Text: "every item named by a transition in the history of `Σ`, retracted ones included: … A retracted observation stops supplying a record but keeps its item in the universe".
- Ambiguity: the oracle's input describes only the transitions in force, so it cannot see the history.
- Reading: `PiState` takes an optional `historyItems?: readonly Item[]`, the items named by past transitions that are no longer in force (a retracted observation, and once `Withdraw` is specified, a withdrawn incompatibility or collapse). They are tracked like the items of current transitions, so they and their closure belong to `U(Σ, Q)`, but they supply no Base record and no constraint; rules still give them records derived from current grounds. The oracle derives no item from them: the caller lists every item a past transition named, so a past collapse of `A` contributes both `A` and `A → ⊥`. Items already tracked by the current state may be repeated; duplicates are ignored. Tested in `test_oracle_retracted_observation_keeps_its_item`.
- Alternative: a structured history (`{ observations, incompatibilities, collapses }` of past transitions) from which the oracle derives the tracked items itself.

**A24. A closure listed for `⊥_B` is ignored, not rejected.** `[Exploratory]`
- Text: item 7, "`CloseDomain(D)`: Register in `C_B`, for a boundary `D ≠ ⊥_B`, …"; item 14, `∀` generic and the `∃` exclusion require "`CloseDomain(D)` in `C_B`, `D ≠ ⊥_B`".
- Ambiguity: item 7 now makes `CloseDomain(⊥_B)` unregistrable, so a state listing it is not reachable; A16 rejects other unreachable states.
- Reading: the oracle still accepts `⊥_B` in `closedDomains` and lets item 14's side condition `D ≠ ⊥_B` make it ground nothing (A13, tested in `test_oracle_vacuous_grounding_requires_non_bottom_domain`). This keeps the oracle's result defined on any state the differential test generates.
- Alternative: reject such a state, as A16 does for `+⊥` and undeclared boundaries.

**A25. `Dom(D)` is read from the boundary system.** `[Exploratory]`
- Text: item 6, "**Domain Monotonicity**: whenever `B' ⊑ B`, `Dom(B') ⊆ Dom(B)`; … a boundary with several parents admits only handles common to all of them".
- Reading: the oracle takes `Dom(D)` from `BoundarySystem.handlesOf(D)` and does not enforce monotonicity itself, so quantifier instances, structural reflexivity and congruence rewrites follow whatever the boundary system admits. At `9c0fd4d`, `defineBoundary` without explicit handles gives a boundary the union of its parents' handles, and explicit handles are not checked against the parents; until the boundary system enforces item 6, a state built that way can give the oracle a domain that item 6 excludes.
- Alternative: the oracle checks monotonicity over `𝔅(Σ)` and rejects a violating state (A16).

## Readings of items 4 and 14 as amended in `5a385ce`

**A26. Overlap is read from `BoundarySystem.meetStatus`.** `[Exploratory]`
- Text: item 4, "two boundaries are **known to overlap** when one refines the other, a meet is registered for them, or they have a unique maximal registered common sub-boundary …; they are **disjoint** (`B₁ ⊓ B₂ = ⊥_B`) only when one of them is `⊥_B` or disjointness is declared for them or inherited from declared ancestors; otherwise their overlap is **unknown**".
- Ambiguity: the oracle's state description carries no registry of meets and disjointness declarations of its own; the boundary system holds them.
- Reading: the oracle classifies a pair of `𝔅(Σ)` by `meetStatus(B₁, B₂)` as a known overlap with the meet it names, disjoint, or unknown, and never calls `meet`, which gives `⊥_B` for both of the last two. It does not re-derive item 4's conditions; as for `Dom(D)` (A25), it follows whatever the boundary system reports.
- Alternative: re-derive the three cases from `refines` and the registered meets and disjointness declarations, which the boundary system does not expose.

**A27. Scoped Cut is the only rule of item 14 that reads an overlap.** `[Exploratory]`
- Text: item 4, "An unknown overlap is not disjointness: it never satisfies a disjointness premise, licenses no Scoped Cut, and opposite records across it carry an `OverlapUnknown` obligation"; item 14, the Scoped Cut side condition "`B₁` and `B₂` known to overlap (item 4)".
- Reading: Scoped Cut fires only for a known overlap, at its meet, so a disjoint pair and a pair of unknown overlap both license nothing. No other row of item 14 consults `⊓` (heredity, `obs`, Incompatibility and Congruence use `⊑`; covers are A32), and no row has a disjointness premise, so the three-valued meet changes nothing else in `Π(Σ)`: no record crosses an unknown overlap, and the oracle adds no atom for it. Tested in `test_oracle_scoped_cut_needs_known_overlap`.
- Alternative: none found in the text. Item 9's Meet Collision Corollary follows from heredity, which item 14 governs.

**A28. Shape and order of `OverlapUnknown`.** `[Exploratory]`
- Text: item 14, Reporting, "For two boundaries whose overlap is unknown (item 4), each item `A` with a present `+A` record on one and a present `-A` record on the other carries an obligation `OverlapUnknown(B₁, B₂, A)`".
- Ambiguity: "one … the other" leaves the order of `B₁` and `B₂` open, and a pair can meet the condition in both directions.
- Reading: `PiModel.overlapObligations: readonly { left: string; right: string; item: Item }[]`, one entry per unordered pair of distinct boundaries and item, whichever boundary holds `+A`, and one entry even when both directions hold. `left` precedes `right` in `PiModel.boundaries` (the boundary system's order: `⊤_B`, then declaration order), and the list is sorted by `left`, then `right`, then the item's place in `U(Σ, Q)`. An entry does not say which boundary holds `+A`. Tested in `test_oracle_unknown_overlap_records_obligation_without_collision`, where the left boundary holds the exclusion, and `test_oracle_overlap_obligations_follow_present_records`.
- Alternatives: ordered pairs with `B₁` holding `+A`, which reports a pair twice when both directions hold; or pairs ordered by name.

**A29. The records that raise `OverlapUnknown`.** `[Exploratory]`
- Text: as A28, and Reporting, "A record of `(B, p, A)` is **present** when `rec(B, p, A)` is true in `M`".
- Reading: literal. Presence is G4b's, so a merely possible record (`rec` undefined) raises no obligation, although an undefined `coll` is reported as `Collision`. Authority and origin do not matter: a `Quarantined` or `Undetermined` record counts, and so does a record inherited by heredity, so one conflict raises an obligation for every pair of unknown overlap among the boundaries below its two records. An obligation is raised even when one or both slots are themselves in `Collision`, so two colliding sibling boundaries of unknown overlap raise one. The obligation is not `Rev(B, A)`: it does not enter `revisionObligations`, sets no row's `revisionObligation` and changes no local status. Tested in `test_oracle_overlap_obligations_follow_present_records` and `test_oracle_ambiguous_meet_is_an_error_where_needed`.
- Alternatives: count possible records too, as `Collision` counts an undefined `coll`; count only `Live` records, or only records of base observations; skip a pair when either slot collides, since the conflict surfaces there already (the Reporting sentence's reason, "since no boundary holds both records", describes the case where neither slot collides).

**A30. Pairs with `⊤_B`, and a boundary with itself, never have an unknown overlap.** `[Exploratory]`
- Text: item 4, "**Top (`⊤_B`)**: unrestricted global frame (`B ⊑ ⊤_B` for all `B`)" and "known to overlap when one refines the other".
- Reading: every pair with `⊤_B` is a known overlap, as is every pair in which one boundary refines the other, and a pair `(B, B)` is never considered, since a conflict on one boundary is a `Collision`. Records on `⊤_B` therefore never raise `OverlapUnknown` themselves; they reach the sub-boundaries by heredity, whose pairs may. `𝔅(Σ)` holds only non-empty boundaries, so the `⊥_B` case of disjointness never arises among its pairs. Tested in `test_oracle_overlap_obligations_follow_present_records`.
- Alternative: none found in the text.

**A31. Where an ambiguous meet is an error.** `[Exploratory]`
- Text: item 4, "(several call for a registered meet)"; item 14, Role, "where a meet the program needs is ambiguous, it reports an error instead of returning a truncated or guessed result".
- Ambiguity: a pair with several maximal registered common sub-boundaries meets none of item 4's conditions for a known overlap, so "otherwise their overlap is unknown" would apply literally, although the two boundaries share non-empty sub-boundaries. Item 14 does not say which uses of a pair need its meet.
- Reading: the oracle never classifies an ambiguous pair; it throws where the pair's status is needed. Scoped Cut needs the meet of every pair of `𝔅(Σ)` once `U(Σ, Q)` holds an implication, as under A11, and the reporting needs the status of a pair holding opposite present records. A state whose ambiguous pairs are needed for neither is evaluated. Tested in `test_oracle_ambiguous_meet_is_an_error_where_needed`.
- Alternatives: count the pair as a known overlap without an obligation, since its common sub-boundaries receive both records by heredity and collide; count it as unknown, following "otherwise" literally; throw for any ambiguous pair of `𝔅(Σ)`.

**A32. Cover pullbacks across an unknown overlap are left to the boundary system.** `[Exploratory]`
- Text: item 5, Meet-Stability, "If `{B_i} ▷ B` and `B' ⊑ B`, then `{B_i ⊓ B' | B_i ⊓ B' ≠ ⊥_B} ▷ B'`"; item 4, an unknown overlap "never satisfies a disjointness premise"; item 14, Pending interfaces, "the registered covers of item 5 stand in for witnessed covers".
- Ambiguity: when `B_i` and `B'` have an unknown overlap, `B_i ⊓ B'` is neither known to be `⊥_B` nor a known boundary, so the pulled-back family is not determined.
- Reading: the oracle takes the witnessed covers from `BoundarySystem.witnessedCoversOf` (A10) and does not check how they were computed. At `5a385ce` its Meet-Stability step calls `meet`, which gives `⊥_B` for an unknown overlap, so the cell is dropped from the pulled-back cover. Example: `{B1, B2} ▷ B` with `B1` and `B2` declared disjoint, `X ⊑ B`, and `Y` with parents `B1` and `X`; the overlap of `B2` and `X` is unknown, so `witnessedCoversOf(X)` holds `{Y}`, and Cover-Gluing lifts a `Live` `+P` on `Y` to a `Live` `+P` on `X`, which item 5 supports only if `X` does not overlap `B2`. The oracle reproduces that result. It is not tested, because it rests on the dropped cell rather than on item 5. Once `meet` throws for an unknown overlap, `witnessedCoversOf`, and with it the oracle, will throw for such a state.
- Alternatives: the oracle rejects any state in which a cover's cell has an unknown overlap with a sub-boundary of the covered boundary; or a cover with such a cell has no pullback to that sub-boundary, which needs the registered covers that the boundary system does not expose.
- Status: item 5's Meet-Stability now states the second alternative: a cell whose overlap with `B'` is unknown leaves the cover without a base change to `B'`. `witnessedCoversOf` follows it, so in the example `X` has no derived cover, the oracle evaluates the state without lifting `+P`, and nothing throws. The oracle's code is unchanged; the reading stays `[Exploratory]` until the maintainer rules on it.
