# 1710 — Laguerre target reconnected to the committed compact-kernel consumer

Date: 2026-09-20.

Status: formal interface audit; no carrier theorem and no RH claim.

The fixed-scale Laguerre candidate from record 1709 was checked against the
committed Lean interfaces. The carrier transport is already formal in
`SoninCarrierMultiplierConjugate`: carrier nontriviality is equivalent to a
nonzero radial vector whose multiplier conjugate equals the reflected vector
up to sign. The compactness upgrade is already formal in
`C1CarrierCompactObservableWitness`: a bounded approximate-kernel sequence,
vanishing under the defect operator, and a compact observable that does not
converge to zero produce a nonzero kernel vector.

Therefore the producer target is not a new transport brick. It is the one
fixed-scale analytic package:

1. identify the committed Gamma-symbol defect operator on the Laguerre prefix;
2. construct bounded normalized approximate kernels with defect tending to
   zero, using the continuous half-line formulas rather than a grid;
3. prove that one fixed compact observable has a nonzero limiting output.

The finite-section tables in records 1639--1642 remain candidate evidence only.
They do not establish any of these three statements. This audit narrows the
fastest carrier attack without changing the binding route map or claiming
`SourceRH`/RH.
