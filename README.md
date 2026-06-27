# Connes-Weil RH Proof

This repository is the formal working area for the Connes-Weil Riemann
Hypothesis proof project.

It separates the final manuscript and future formalization work from the
larger control/archive repository. The control repository remains the place
for route history, experiments, scratch diagnostics, and bus-level memory.
This repository keeps only the material needed to turn the current
Connes-Weil proof draft into a referee-readable paper and then a Lean
formalization.

## Current Artifact

The current manuscript draft is:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md
```

Current status:

```text
v0.1 referee-readable source-conditional manuscript
```

The manuscript states its own boundary. It is not a public proof certificate,
journal acceptance, Clay acceptance, or Lean formalization.

## Repository Layout

```text
docs/
  manuscripts/
    connes-weil-rh-proof-draft.md

formalization/
  README.md

AGENTS.md
MEMORY.md
README.md
```

## Working Rules

- Keep the manuscript and formalization work in this repository.
- Keep route-search history and broad control notes in the control/archive
  repository.
- Do not publish a breakthrough claim from this repository until the manuscript
  has passed independent source-line rereading and hostile mathematical review.
- Treat Lean formalization as a second phase after the manuscript proof chain
  has a stable paper form.
