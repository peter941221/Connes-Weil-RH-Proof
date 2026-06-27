# AGENTS.md

## [1] Project Overview

This repository is the dedicated working area for the Connes-Weil RH proof
manuscript and its future Lean formalization.

The control/archive repository keeps route history, experiments, and broad
project memory. This repository keeps the formal proof artifact:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md
```

Current status:

```text
v0.1 referee-readable source-conditional manuscript
```

This status does not claim journal acceptance, Clay acceptance, or Lean
verification.

## [2] Commands

There is no build system yet.

Useful checks:

```text
git status --short
git diff --check
rg -n "task-marker|fix-marker|proof-sketch|named-gap" docs
rg -n "[^\x00-\x7F]" docs
```

When Lean work begins, add the exact Lake commands here after they run
successfully in this repository.

## [3] Project Structure

```text
docs/manuscripts/
  Drafts and paper-facing manuscript files.

formalization/
  Future Lean 4 formalization workspace notes and setup.

README.md
  Public-facing repository overview.

MEMORY.md
  Local project memory and audit history.
```

## [4] Coding And Writing Conventions

- Keep mathematical claims source-backed.
- Distinguish source theorems, project lemmas, and external certification.
- Do not blur internal route-paper closure with public proof certification.
- Prefer theorem/lemma statements with explicit dependencies over prose-only
  claims.
- Keep manuscript text ASCII unless a target journal format requires otherwise.

## [5] Git, Branching, And PR Norms

- Keep commits focused on manuscript, formalization, or project documentation.
- Do not mix control/archive experiments into this repository.
- Commit major manuscript or formalization milestones.
- Before commit or push, check staged files and staged diff for accidental
  control/archive artifacts.

## [6] Environment, Secrets, And Deployment

- Do not commit credentials, local machine paths, or private workflow artifacts.
- This repository is private by default.
- Public communication about the proof requires separate review.

## [7] Known Pitfalls

- The manuscript is source-conditional. It depends on the cited CCM24, CCM25,
  and CC20 source theorems as stated.
- The current artifact is not a Lean proof.
- The current artifact is not a Clay or journal certificate.
- Route-search notes belong in the control/archive repository unless they are
  directly needed by the manuscript or formalization.
