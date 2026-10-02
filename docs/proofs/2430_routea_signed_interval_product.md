# 2430 — Route A signed interval product

Date: 2026-10-02.

`RealInterval2429.mem_mul` now proves the exact four-corner product hull used
by `iprod`, including intervals crossing zero.  The proof uses the ordered
`uIcc` image theorem from Mathlib: for a fixed factor, the two possible
endpoint products are enclosed by the corresponding two corner products, and
the sign of the varying factor selects the lower/upper endpoint order.

The theorem was independently compiled with Lean 4.30 and the current
Mathlib build.  It is an algebraic enclosure theorem only; directed MPFR
rounding, `ciprod`, and the identification with `correctedPhysical` remain
separate obligations.  No numerical artifact is imported.
