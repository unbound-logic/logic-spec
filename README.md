# `unbound-logic/logic-spec`

Living specification for an end-to-end logic system (`UL-Core`) designed from first principles under a zetetic (inquiry-driven) perspective—defaulting neither to Platonism nor to pure formalism, and recovering minimal constructive, intuitionistic, and classical first-order logic as explicit boundary specializations.

## Reading Map

- **[AGENTS.md](AGENTS.md)** — Epistemic stance, five reasoning guardrails (Anti-Inertia Audit, Constructive Socratic Challenge, Terminology Hygiene, Anti-Triviality Test, Hypothesis vs. Consensus), language split, and workflow rules.
- **[spec/core.md](spec/core.md)** — Normative formal specification of `UL-Core` (v0.1.0): role-indexed content grammar, boundary meet-semilattice & finitary covers, inquiry state transitions (`M1`/`M2`/`Retract`), dual-polarity provenance calculus, Quarantine, Curry Paradox firewall, and the four-tier specialization spectrum (`UL-Core` ⊃ `UL-Minimal` ⊃ `UL-Intuitionistic` ⊃ `UL-Classical`).
- **[spec/worked-examples.md](spec/worked-examples.md)** — Step-by-step formal derivations and adversarial stress-tests validating `spec/core.md` across multi-regime collision/quarantine, M1/M2 anti-immunization, Curry attacks, and classical recovery.
- **[docs/design-review.md](docs/design-review.md)** — Decision ledger recording every foundational design choice, rejected alternatives, and falsifiable `Reopen if:` conditions.
- **[docs/glossary.md](docs/glossary.md)** — Terminology registry separating quarantined classical terms from defined local primitives.

## Specification Verification

This repository verifies cross-references, claim statuses, and register integrity with `@spec-family/spec-graph` (Node 22+):

```bash
npm ci
npm run spec-graph
```
