# 2393 — directed span partition interface

Date: 2026-10-02.

The directed-accumulation interface now has a slice-shaped form matching the
replay: each span has an explicit start and length.  The theorem requires an
explicit partition equality between the global finite sum and the concatenated
span sums, then propagates termwise and per-span upper bounds to the global
upper bound.

This exposes, rather than hides, the remaining numerical obligations: prove
the termwise directed dominance and prove the span partition equality for the
actual ordered replay.  No numeric value is imported.
