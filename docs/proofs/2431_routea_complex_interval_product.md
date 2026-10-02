# 2431 — Route A complex interval product

Date: 2026-10-02.

The Lean interval layer now contains `ComplexRect2427.mem_mul`.  Its real
component is the signed interval product difference
`Re(a)Re(b) - Im(a)Im(b)`; its imaginary component is the interval sum
`Re(a)Im(b) + Im(a)Re(b)`.  The proof is assembled from the previously
verified real four-corner product, interval addition, and interval subtraction
lemmas, matching the structure of `ciprod`.

The source and its axiom audit compile independently with Lean 4.30 and the
current Mathlib build.  This remains an algebraic enclosure layer: MPFR
rounding and the mathematical `correctedPhysical` term are not yet connected.
