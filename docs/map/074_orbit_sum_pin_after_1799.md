# 074 — Orbit-sum pin realized; phase law dictates the analytic shape

Status: the geometry pin is realizable and the gate at the pinned head is a
phase balance (2026-09-21).

Record [1799](../proofs/1799_orbit_sum_pin_and_phase_law.md) instantiates the
committed `OrbitG8Geometry` interpolation system exactly (16/16 cases:
residual ≤ 3.2e-8, centered orbit sum = −2.000000) at right-hand off-line
zeros, and reads `ICgate(g*⋆g)` at the pinned head.

- **W1**: the pin exists — orbit values, detector node, healthy zeros and
  the orbit sum are realized by an explicit compactly-supported family.
  The 1798 toy-pin misgiving (free λ outside the feasible window) is
  superseded: the real system pins a point, and it exists.
- **W2**: at the pinned head the gate is dominated by prime cells and is a
  multi-frequency quasiperiodic function of the zero height (sign flips at
  γ ≈ 20.5, 28, 36; single-phase cos(2γ log 2) fit fails by 12×). No
  pointwise-in-the-head signed statement survives; the C3 signed estimate
  must be phase-locked: cross channel against a carrier-locked reference,
  or Schwartz θ-regularized (1734/F59 two-IBP tool).
- **W3**: the Archimedean face is small and stable — the balance is all
  prime side, matching the B5 budget shape.
- **W4**: as β → ½⁺ the orbit nodes ρ and 1−ρ̄ coalesce with colliding
  targets (1 vs −1): the system degenerates like 1/ε at the critical line;
  the RH passage must be the off-line budget limit, not an on-line pin.

Instrument laws from the in-build errata: static-width basis singular at
height γ (E-E), block-split solve amplifies Gevrey leakage (E-F),
spectral-root base ring invisible to splines — zeros must be constructed by
a nullspace bump combination (E-G), direct Archimedean engine invalid on
oscillatory profiles — σ engine is the referee (E-H).

Next active target: the carrier-locked two-span signed estimate (C3′) on
paper — cross-gate domination of the phase-sensitive prime cells, with the
σ-identity arch face as floor and the two-IBP bound as the pairing tool.
