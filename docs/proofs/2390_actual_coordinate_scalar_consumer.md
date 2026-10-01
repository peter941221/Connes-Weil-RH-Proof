# 2390 — actual-coordinate scalar consumer

Date: 2026-10-02.

The Lean interface now matches the 2386 ledger directly: actual-coordinate
node bounds, a uniform coordinate-transfer charge, and an actual composite
scalar bound imply the final corrected-physical `stripNorm` scalar bound.
The transfer charge is consumed by the audited finite-sum identity, not
manually added outside the theorem. All numerical hypotheses remain explicit
inputs.
