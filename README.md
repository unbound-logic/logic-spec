# `unbound-logic/logic-spec`

Living specification for an end-to-end logic system (`UL-Core`) designed from first principles under a zetetic (inquiry-driven) perspective—defaulting neither to Platonism nor to pure formalism, and recovering minimal constructive, intuitionistic, and classical first-order logic as explicit boundary specializations.

## Reading Map

- **[AGENTS.md](AGENTS.md)** — Epistemic stance, five reasoning guardrails (Anti-Inertia Audit, Constructive Socratic Challenge, Terminology Hygiene, Anti-Triviality Test, Hypothesis vs. Consensus), language split, and workflow rules.
- **[spec/core.md](spec/core.md)** — Normative formal specification of `UL-Core` (v0.1.0, `Consensus`): role-indexed content grammar (`G3`), boundary meet-semilattice & finitary covers, inquiry state transitions (`M1`, `M2`, `Retract`), dual-polarity provenance calculus, Quarantine, Curry Paradox firewall, and the four-tier specialization spectrum (`UL-Core` ⊃ `UL-Minimal` ⊃ `UL-Intuitionistic` ⊃ `UL-Classical`).
- **[spec/worked-examples.md](spec/worked-examples.md)** — Step-by-step formal derivations and adversarial stress-tests (`Consensus`) validating `spec/core.md` across multi-regime collision/quarantine, `M1` & `M2` anti-immunization, Curry attacks, and classical recovery.
- **[spec/metatheory.md](spec/metatheory.md)** — Active formal metatheory specification (`Consensus` for well-foundedness `MT-1`, Curry firewall `MT-2`, non-explosion & `⊥` safety `MT-3`, disjoint zero-leakage `MT-4`, cover stability `MT-5`, `Retract` purity `MT-6`, and classical `2`/`2^k` recovery `MT-9`; `Exploratory` for `M1(ii)` proxy limits `MT-7` and syntactic completeness `MT-8`).
- **[docs/design-review.md](docs/design-review.md)** — Decision ledger recording every foundational design choice, rejected alternatives, and falsifiable `Reopen if:` conditions.
- **[docs/glossary.md](docs/glossary.md)** — Terminology registry separating quarantined classical terms from defined local primitives.

## Reference Kernel & Adversarial Test Suite

The executable TypeScript reference kernel (`src/`) and test suite (`test/`) run with zero runtime dependencies on Node 22+:

- `src/syntax.ts` — Role-indexed atomic grammar (`G3`), compound items, structural impossibility shorthand (`¬_⊥`), handle substitution, and single-definition Curry firewall checks.
- `src/boundary.ts` — Bounded meet-semilattice `(B, ⊑, ⊓, ⊤_B, ⊥_B)`, finitary Grothendieck exhaustive covers, native relation scoping, and handle individuation (`I_B`).
- `src/engine.ts` — Dual-polarity fixpoint engine (`⊩⁺` / `⊩⁻`), well-founded DAG provenance, Inference Quarantine, Scoped Cut, `Observe` / `Retract` / `RefineBoundary`, and `M1` / `M2` enforcement.
- `src/specializations.ts` — Closure verification and evaluation for `UL-Minimal`, `UL-Intuitionistic`, and `UL-Classical`.
- `test/syntax-and-curry.test.ts` — Grammar, reserved forms, and four Curry attack vector stress-tests.
- `test/boundary-and-inquiry.test.ts` — Semilattice, cover axioms, co-reference isolation, pure `Retract`, `ℝ \ {0}`, and `swan_402` tests.
- `test/calculus-and-quarantine.test.ts` — DAG well-foundedness, symmetric downward heredity, Quarantine, Scoped Cut, and cover gluing tests.
- `test/specializations.test.ts` — Four-tier specialization and classical recovery derivations (`4A`–`4C`).

## Verification

This repository checks type safety, kernel behavior, cross-references, claim evidence bindings, mutation resistance, and orientation integrity (Node 22+):

```bash
npm ci
npm run verify
```

`npm run verify` runs six sequential gates declared in `package.json`:

1. `npm run typecheck` — Erasable TypeScript check (`tsc --noEmit`).
2. `npm test` — Node test runner executing all four adversarial suites in `test/`.
3. `npm run spec-graph` — Verifies specification graph links, `README.md` orientation paths/commands, and `docs/design-review.md` registers.
4. `npm run spec-guard` — Runs all `@assert-count` assertions binding `spec/core.md`, `spec/worked-examples.md`, and `spec/metatheory.md` to executable tests.
5. `npm run spec-guard:prove` — Mutation/fault-injection proof verifying every `@assert-count` rule catches failing implementations.
6. `npm run spec-guard:claims` — Audits `Consensus` vs. `Exploratory` claim evidence across `spec/`.
