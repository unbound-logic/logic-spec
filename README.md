# `unbound-logic/logic-spec`

Living specification for an end-to-end logic system (`UL-Core`) designed from first principles under a zetetic (inquiry-driven) perspective—defaulting neither to Platonism nor to pure formalism, with minimal constructive, intuitionistic, and finite-domain classical specializations obtained as explicit boundary closures.

## Reading Map

- **[`unbound-logic` charter](https://github.com/unbound-logic/.github/blob/main/CHARTER.md)** — Organization-wide design principles, each with the ratified decisions it rests on.
- **[AGENTS.md](AGENTS.md)** — Epistemic stance, five reasoning guardrails (Anti-Inertia Audit, Constructive Socratic Challenge, Terminology Hygiene, Anti-Triviality Test, Claim Status Ladder), language split, and workflow rules.
- **[spec/core.md](spec/core.md)** — Normative formal specification of `UL-Core` (v0.2.0; each item labelled `Exploratory`, `Decided`, `Tested`, or `Proved`): role-indexed content grammar (`G3`), boundary meet-semilattice & finitary covers, inquiry state transitions (`M1`, `M2`, `Retract`), dual-polarity provenance calculus, Quarantine, Curry Paradox firewall, and the four-tier specialization spectrum (`UL-Core` ⊃ `UL-Minimal` ⊃ `UL-Intuitionistic` ⊃ `UL-Classical`, the last restricted to finite domains).
- **[spec/worked-examples.md](spec/worked-examples.md)** — Step-by-step formal derivations and adversarial stress-tests exercising `spec/core.md` across multi-regime collision/quarantine, `M1` & `M2` anti-immunization, Curry attacks, and classical recovery.
- **[spec/metatheory.md](spec/metatheory.md)** — Metatheory of `UL-Core` (`MT-1`–`MT-9`: well-foundedness, Curry firewall, non-explosion & `⊥` safety, disjoint zero-leakage, cover stability, `Retract` purity, `M1(i)–(iii)` / `M2` anti-immunization + Formal Horizon Corollary, the `NJ_min` / `NJ` rule sets of the proof checker, and finite-domain classical `2`/`2^k` valuation). MT-9 is `Proved` after maintainer review; most other results are `Tested`, and the rest are `Decided` or `Exploratory` pending the fixes recorded in `docs/design-review.md` §7.
- **[docs/design-review.md](docs/design-review.md)** — Decision ledger recording every foundational design choice, rejected alternatives, and falsifiable `Reopen if:` conditions.
- **[docs/glossary.md](docs/glossary.md)** — Terminology registry separating quarantined classical terms from defined local primitives.

## Reference Kernel & Adversarial Test Suite

The executable TypeScript reference kernel (`src/`) and test suite (`test/`) run with zero runtime dependencies on Node 22+:

- `src/syntax.ts` — Role-indexed atomic grammar (`G3`), compound items, structural impossibility shorthand (`¬_⊥`), handle substitution, cross-stage reflection AST (`Refl_k@Σ_t` / `reflStatus`), and single/mutual-recursion Curry firewall checks.
- `src/boundary.ts` — Bounded meet-semilattice `(B, ⊑, ⊓, ⊤_B, ⊥_B)` with disjoint/meet consistency checks, domain monotonicity (a sub-boundary's handles are a subset of every declared parent's; a boundary with several parents defaults to the handles common to all of them), deep snapshots (`clone()`), finitary Grothendieck exhaustive covers registered under identifiers (`registerCover`, `withdrawCover`) and re-validated against the current boundaries (`coverValidity`: valid, invalid or unverified), whose closure starts from the covers that are not invalid (`verifiedOnly` keeps the valid ones alone) and reports an error instead of truncating at its pass or 16-cell bound, native relation scoping, and handle individuation (`I_B`).
- `src/engine.ts` — Projection of the evaluation program `Π(Σ)` of [core.md](spec/core.md) §5 item 14: grounds its rule table over `𝔅(Σ) × U(Σ, Q)` (`⊥`, every item named by a past transition, retracted ones included, and the queried items, closed under sub-items, quantifier instances and one-position congruence rewrites), computes the well-founded model by the alternating fixpoint, and reports local status (`localStatus`; `Collision` when the collision atom is true or undefined), authority (`authorityOf`: `Live` / `Undetermined` / `Quarantined`, with `isLive`), obstruction and revision obligations, while provenance entries (`allGrounds` / `liveGrounds`) are finite derivations that witness true atoms; an ambiguous meet that Scoped Cut needs, or witness enumeration beyond its bound, is reported as an error. Also an immutable stage & boundary trace archive (`evaluateAtStage`) with operational cross-stage reflection (`isReflectionWellScopedAtStage`), recorded theorems anchored to base and intermediate grounds, `Observe` / `Retract` / `Constrain` / `WitnessCover` / `CloseDomain` (enumerative `∀` / `∃` grounding only on a closed domain `D ≠ ⊥_B`) / `RefineBoundary` / `Withdraw` (each constraint of `C_B` carries an identifier; `withdraw` is refused under `monotoneOnly`), cover obligations (`coverObligations`), and `M1(i)–(iv)` / `M2` enforcement. `Dom(D)` is fixed when `D` is defined, so a closure's anchored handle set cannot change in the kernel.
- `src/deduction.ts` — Prawitz-style natural deduction proof checker (`→I` sub-proof discharge, constrained & open-domain schematic `∀I` / `∀E` / `∃I` / `∃E` with strict bound-variable & eigenvariable freshness, `Cover-Gluing`, `refl-intro`, and `UL-Intuitionistic`-gated `⊥E`) bridged to `InquiryEngine` with full base and intermediate ground dependencies.
- `src/specializations.ts` — Closure verification (`monotoneOnly`, reachable `No-Gaps`, `domainConstraint`, compound exclusion consistency, and (C3) closed, non-empty quantifier domains within each atomic cell of a valid cover whose cells have known overlaps) and `2`/`2^k` evaluation for `UL-Minimal`, `UL-Intuitionistic`, and `UL-Classical`.
- `test/syntax-and-curry.test.ts` — Grammar, reserved forms, single and mutual-recursion Curry attack stress-tests.
- `test/boundary-and-inquiry.test.ts` — Semilattice, cover axioms, domain monotonicity, `CloseDomain`-gated enumerative quantifiers, cover re-validation, `Withdraw`, co-reference isolation, pure `Retract`, Quarantine reinstatement, `ℝ \ {0}`, `swan_402`, and `M1(iii)` anti-proxy excess-content tests.
- `test/calculus-and-quarantine.test.ts` — DAG well-foundedness, symmetric downward heredity, stratified Quarantine, `⊥` safety, Scoped Cut, and cover gluing tests.
- `test/deduction.test.ts` — Standalone `Cover-Gluing`, `→I` combinators & anti-vacuity, open-domain `∀I`/`∃E` eigenvariable checks, and `UL-Minimal` vs. `UL-Intuitionistic` tests.
- `test/reflection.test.ts` — Immutable stage archive traces, nested `Refl_k@Σ_t` meta-reasoning, Vector 2 operational Curry immunity, and `refl-intro` stratification tests.
- `test/specializations.test.ts` — Four-tier specialization and classical `2`/`2^k` recovery derivations (`4A`–`4C`), including the (C3) closed, non-empty domain and valid cover requirements.
- `test/property-fuzz.test.ts` — Deterministic seeded property-based fuzzing suite (`Mulberry32`, configurable via `UL_FUZZ_SEED` / `UL_FUZZ_MULTIPLIER`) stress-testing `MT-1`–`MT-9` across semilattice/cover axioms, biased `G-15` conflict graphs, disjoint survival, stage-archive reflection, capture-avoiding substitution & deduction constraints, `UL-Classical` `2`/`2^k` recovery, and `M1`/`M2` anti-immunization.
- `test/oracle/pi-sigma.ts` and `test/oracle.test.ts` — Clean-room oracle of the evaluation program `Π(Σ)` (core.md §5 item 14), written from the specification alone, with hand-computed cases; its ratified readings are recorded in `test/oracle/AMBIGUITIES.md`.
- `test/differential.test.ts` — Seeded differential comparison of the kernel with the oracle (configurable via `UL_FUZZ_SEED` / `UL_FUZZ_MULTIPLIER`): on random states over random boundary topologies (a diamond `B`, `B1`, `B2`, `B12`, siblings of unknown overlap, declared disjoint siblings, and an optional unrelated `C`) they must agree on `U(Σ, Q)`, on local status, authority, obstruction and revision obligations for every slot, and on `OverlapUnknown` obligations.

### Metatheory-to-kernel map

Non-normative notes on where the reference kernel implements each result of [spec/metatheory.md](spec/metatheory.md).

- **MT-1** — `src/engine.ts` builds the evaluation program `Π(Σ)` of `spec/core.md` §5 item 14 over `𝔅(Σ) × U(Σ, Q)`, computes its well-founded model by the alternating fixpoint, reports it under G4b (`localStatus`, `isLive`, `authorityOf`), and throws instead of truncating. `test/differential.test.ts` compares it slot by slot with the clean-room oracle `test/oracle/pi-sigma.ts`.
- **MT-2** — `src/syntax.ts` (`checkRecursiveDefinitionSystem`, `collectBoundaryRefs`); `src/engine.ts` (`evaluateAtStage` over an immutable stage archive that snapshots the inquiry state and `BoundarySystem.clone()`, evaluating cross-stage reflection against a frozen stage `0 ≤ t < currentStage` with `level(J) ≤ k` and stage-`t` boundary admissibility via `isReflectionWellScopedAtStage`); `src/deduction.ts` (`refl-intro`).
- **MT-3** — `src/engine.ts` rejects `Observe⁺(B, ⊥)` on non-empty boundaries, introduces `-(A → C)` one way from a `Live +A` and a `-C` record, and gates `imposs-excl` on `Live +(A → ⊥)`; under a self-refuting pair `+A`, `+(A → ⊥)` a `+⊥` record is at most possible, never present or `Live`.
- **MT-4** — `BoundarySystem.meetStatus` in `src/boundary.ts` reads the registry open-world (overlap, declared disjointness, or unknown); `meet` throws for an unknown overlap, and the Meet-Stability step of `witnessedCoversOf` derives no cover of a sub-boundary that a cell overlaps unknownly. `src/engine.ts` fires Scoped Cut only on known overlaps and reports `overlapObligations()`.
- **MT-5** — Cover-Gluing in both polarities in `src/engine.ts`, and the `cover-glue` rule of `src/deduction.ts`; `witnessedCoversOf` in `src/boundary.ts` starts from the registered covers that are not invalid, and `src/engine.ts` reports `coverObligations()`.
- **MT-6** — `retract` and `withdraw` in `src/engine.ts` delete a base observation or a constraint of `C_B` by identifier and add nothing; the stage archive keeps the states before them.
- **MT-7** — `refineBoundary` in `src/engine.ts` checks M1(i)–(iv): indirect reference through a relation-dependency graph of incompatibilities, structural collapses and `Live` conditionals, and domain binding of the criterion to the refined boundary; admitted refinements stay in the stage record, and `refinementObligations()` reports kept handles that later carry `Live -δ`. A handle is contingent when its `HandleSpec.kind` in `src/boundary.ts` is `"contingent"`.
- **MT-8a** — `src/deduction.ts` (capture-avoiding `substituteHandle` with bound-variable freshness checks on `∀I` and `∃E`, lexically scoped `→I` discharge, `→E`, `∧I`/`∧E`, `∨I`/`∨E`, open-domain schematic `∀I`, `∀E`, `∃I`, `∃E` non-escape, standalone Cover-Gluing, `≈_B`, and `UL-Intuitionistic`-gated `⊥E`), with intermediate-node `GroundDependency` anchoring and `@incompat:` provenance in `src/engine.ts`.
- **MT-9** — `src/specializations.ts` enforces `monotoneOnly: true`, (C3)'s witnessed closed non-empty domains with `Dom(D) ⊆ Dom(B*)`, `No-Gaps` over every reachable atom and congruence, the quantifier constraint `[δ]`, and consistency with existing `Live` compound exclusions, and reports `GlobalCoverStatus` (`"+" | "-" | "split"`) with per-cell polarities (`2^k`).

## Verification

This repository checks type safety, kernel behavior, cross-references, claim evidence bindings, and orientation integrity (Node 22+):

```bash
npm ci
npm run verify
```

`npm run verify` runs six sequential gates declared in `package.json`:

1. `npm run typecheck` — Erasable TypeScript check (`tsc --noEmit`).
2. `npm test` — Node test runner executing all nine suites in `test/` (`test/*.test.ts`).
3. `npm run spec-graph` — Verifies specification graph links, `README.md` orientation paths/commands, and `docs/design-review.md` registers.
4. `npm run spec-guard` — Runs all `@assert-count` assertions binding `spec/core.md`, `spec/worked-examples.md`, and `spec/metatheory.md` to executable tests.
5. `npm run spec-guard:prove` — Shows that each `@assert-count` rule fails when the text it counts is removed (in memory). It checks that the rules can fail; it does not mutate the kernel or check what a named test asserts.
6. `npm run spec-guard:claims` — Checks that each claim in `spec/` has the evidence its label requires: `Tested` and `Proved` need an `@assert-count` naming a test, and `Proved` also needs `Proof:` in the claim's own text.

Continuous integration runs `npm run verify` on every push and pull request ([`.github/workflows/verify.yml`](.github/workflows/verify.yml)). Long fuzzing runs are started by hand on GitHub-hosted runners ([`.github/workflows/fuzz.yml`](.github/workflows/fuzz.yml)).
