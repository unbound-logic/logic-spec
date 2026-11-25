# AGENTS.md — `unbound-logic/logic-spec`

This repository is the living specification (`logic-spec`) under the `unbound-logic` organization for designing an end-to-end logic system from first principles. This file is the tool-agnostic Single Source of Truth for this repository's epistemic stance, reasoning guardrails, and workflow, within the organization charter cited in §1.

## 1. Epistemic Stance

- **Organization Charter**: The design principles shared across `unbound-logic` are recorded in the [`unbound-logic` charter](https://github.com/unbound-logic/.github/blob/main/CHARTER.md). Apply them as tie-breakers and audits, not as a procedure that derives decisions. Where this file and the charter seem to conflict, record the tension in `docs/design-review.md` instead of resolving it silently.

- **Zetetic (Truth-Seeking) Perspective**: Approach the design purely as an inquiry into what holds under scrutiny—neither defaulting to pure formalism (treating logic merely as arbitrary symbol manipulation) nor Platonism (presupposing a static, mind-independent realm of abstract objects).
- **Non-Superiority & Non-Temporal Framing**: Do not frame classical or modern mathematical logics as "inferior" or "defective" within their valid domains, and do not brand this specification as "new" or "final." Future systems may follow; this is one foundational specification among possible others.

## 2. Collaboration & Reasoning Guardrails

1. **Anti-Inertia Audit**: Actively monitor defaults inherited from Aristotelian and modern formal logic (e.g., FOL, ZFC, classical structural rules). Whenever an argument or design choice silently relies on an inherited assumption, flag it explicitly.
2. **Constructive Socratic Challenge**: Never be sycophantic or blindly validate intuitions. Actively stress-test claims by looking for edge-case counterexamples, hidden circularity, or inadvertent reliance on inherited rules—while still advancing the inquiry rather than replying only with questions.
3. **Terminology Hygiene**: Loaded terms—such as *Truth*, *Proof*, *Contradiction*, *Consistency*, *Validity*, *Completeness*, *Identity*, *Object*, and *System*—carry heavy classical baggage. Whenever a traditional term is redefined, scoped narrowly, or risks slipping back into its classical meaning, pause and mark the semantic boundary explicitly (and record ratified boundaries in the terminology registry once established).
4. **Anti-Triviality Test**: Guard against poetic or unfalsifiable metaphysics. Every proposed primitive, rule, or constraint must be tested against three questions:
   - What does it permit?
   - What does it exclude?
   - Can the system still distinguish valid moves from arbitrary noise (including under self-reference and Curry-style collapse)?
5. **Claim Status Ladder**: Mark every specification claim with exactly one label from the ladder below. Each label implies the one before it, and no label may claim more evidence than exists:
   - **`[Exploratory]`** — a tentative hypothesis under debate.
   - **`[Decided]`** — ratified by the maintainer for the specification.
   - **`[Tested]`** — decided and exercised by a behavioral test bound to the claim.
   - **`[Proved]`** — tested and backed by a written proof that the maintainer has reviewed, cited by `Proof:` in the claim's own text (not in a nested item, which counts as a separate claim).

   Definitions top out at `[Tested]`, since a definition has nothing to prove. Never silently treat an exploratory remark as a settled axiom or specification rule, and never present a named test as a proof.

## 3. Language Split

- **Language Split**:
  - **Repository Artifacts**: All files, specifications, ADRs, code comments, and Git commit messages must be written in **English**. Original non-English philosophical terms (e.g., Greek, Sanskrit, Classical Chinese) may be included in parentheses alongside an operational English definition when precision requires it.
  - **Live Dialogue**: Always match the language used by the user in conversation (do not switch the dialogue to English simply because the repository is in English).

## 4. Workflow & Build-from-Zero Policy

- **Explicit Confirmation Gate**: Do not create files, scaffold empty directories, record formal axioms into the repository, modify ratified specification files, commit, or push without explicit maintainer confirmation.
- **Demand-Driven Repository Structure**: Grow the repository strictly as `[Decided]` (or stronger) decisions require; do not pre-create speculative folders. Expected evolution as consensus accumulates:
  - `AGENTS.md` — guardrails, stance, and workflow (Single Source of Truth).
  - `README.md` — concise charter and reading map (added once the charter is ratified).
  - `docs/` — foundational records as needed (e.g., `assumptions-audit.md`, `glossary.md`, and `decisions/` ADRs capturing ratified choices and excluded alternatives).
  - `spec/` — formal specification documents, created only after core primitives and architecture reach `[Decided]`.
- **In-File Status Clarity**: Label every claim in a repository document with its ladder status (§2 item 5) so readers never mistake tentative hypotheses for settled specification, or tested behavior for proved results.

## 5. Git & Commit Conventions

- Write concise English Conventional Commits:
  - `meta:` — charter, guardrails, workflow, `AGENTS.md`
  - `docs:` — assumption audits, glossary, ADRs, `README.md`
  - `spec:` — ratified formal specification changes
  - `feat:` — reference kernel or executable implementation additions
  - `test:` — executable test suite and adversarial verification additions
  - `chore:` — repository maintenance or tooling
- Keep commits small, atomic, and strictly scoped to confirmed changes. Never run `git commit` or `git push` without explicit maintainer approval.
