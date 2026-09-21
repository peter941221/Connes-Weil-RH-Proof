# 077 — Producer anatomy: gate vs window, the width tension

Status: the producer behind the exit theorem is fully anatomized and its
obstacle is quantified as a width tension (2026-09-21).

Record [1801](../proofs/1801_envelope_qform_and_window.md) lands two rigs
and one collapse:

- **Collapse (theorem-grounded)**: the span/matrix format of the exit
  producer is a re-parameterization of one condition. `PRODUCER(ρ) ⟺ ∃ g:
  OrbitG8Geometry ρ g ∧ ICgate(g*⋆g) ≤ 0` (gate-matrix theorem, k = 1).
- **The gate quadratic form is indefinite** on the geometry-preserving
  nullspace family (G_BB straddles zero, sign = prime-face sign, no
  cancellation risk). At γ = 40 the pinned head's own gate is ≤ 0 (the
  W2 trough). At γ = 14.13 the head reads +1.9e4…+7.4e4 and the
  feasible-λ corrections (λ ≲ O(10), see below) cannot dent it.
- **The committed tailStart window is measured EMPTY at all 8 cases**:
  zero-height floor vs Cartwright zero-budget cap (ball formula grows with
  γ via `+2+dist(2,ρ)`), and the tail sup S(T) falls ~10³ per doubling
  while the budget ε²(tS) grows only 4/3 per level. Closing the window
  needs support(g²) ≳ 5 — allowed by the committed structure
  (orbitIndex free, supports ⊆ (−1,1)) but not realized by the narrow
  1799 owners.
- **The exact tension**: gate ⟶ narrow (small prime book), window ⟶
  wide (large support). The producer = does some intermediate width host
  a test with gate ≤ 0 under the full geometry.

Next active target: the wide owner (k = 2–3, full-width corrections,
a ≈ 6) — measure its window (should close) AND its gate; then the gate
minimization over the window-feasible family is the concrete form of the
remaining problem. Cross-domination (maximize |G_AB|) is the parallel
route. A committed-definition revision (ball radius decoupled from
tailStart) is on the table but needs approval.
