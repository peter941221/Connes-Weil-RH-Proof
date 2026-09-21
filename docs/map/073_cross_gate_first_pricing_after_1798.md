# 073 — Cross gate first pricing

Status: first instrument-valid readouts of the two-span C3 cross gate;
the geometry pin is the binding constraint (2026-09-21).

Record [1798](../proofs/1798_twospan_cross_gate_first_pricing.md) prices
`G_AA`, `G_BB`, `G_AB` on L²-normalized admissible families with four
validated engines and machine-precision swap symmetry.

- The cross gate against a triple-vanishing window reference VANISHES
  (|G_AB| ≤ 2.4e-4): the C3 signed estimate is vacuous there and must be
  stated on the interpolation-compatible (non-vanishing) reference class.
- On positive-reference pairs the gate Gram is barely indefinite
  (det = +0.02 .. +0.18); the feasible λ-window is narrow (roots
  [1.476, 2.166] on the representative pair).
- A single-node toy pin lands a factor 5–40 outside that window and reads
  q > 0: the orbit-sum geometry, not the free-λ face, binds the producer.
- Binding cells of the cross gate: prime powers 2 and 3 (+0.409, +0.345);
  the prime tail past n = 5 is dead on these families.

Next active target: instantiate the real orbit-sum pin
(`Σ_{u ∈ centeredFunctionalEquationOrbit} ĝ²(u) = −2` plus target values)
on the same instrument and re-read q at the geometry-pinned coefficients.
Instrument laws from the in-build errata (slice-offset, normalization,
σ-argument, Taylor witness) are recorded in the proof record.
