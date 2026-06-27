2026-06-27

- Created this repository as the dedicated working area for the Connes-Weil RH
  proof manuscript and future Lean formalization.
- Copied the current internal, source-conditional manuscript draft into:
  `docs/manuscripts/connes-weil-rh-proof-draft.md`.
- Established the repository boundary:
  - this repository holds the formal manuscript and future Lean work;
  - the control/archive repository keeps route history, experiments, and
    bus-level memory.
- Current manuscript status:
  `v0.1 referee-readable source-conditional manuscript`.
- Current explicit boundary:
  the manuscript is not a public proof certificate, journal acceptance, Clay
  acceptance, or Lean formalization.

2026-06-27

- Upgraded `docs/manuscripts/connes-weil-rh-proof-draft.md` from an internal
  completed draft to a v0.1 referee-readable source-conditional manuscript.
- Added source-line audit entries based on official arXiv source files:
  CCM24 `mainc2m24fine.tex`, CCM25 `mc2arXiv.tex`, and CC20
  `weil-compo.tex`.
- Expanded Theorem 1 into five referee-checkable steps: positivity,
  support-square transport, trace legality, CCM read-off, and ledger
  collection.
- Added appendices for operator/domain conventions, trace-class and cyclicity
  ledger, source normalization and sign audit, and the finite-set side
  condition.
- Kept the boundary explicit: this is not a public proof certificate, journal
  acceptance, Clay acceptance, or Lean formalization.
