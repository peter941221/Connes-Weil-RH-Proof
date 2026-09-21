# 076 — Producer anatomy: gate measurement, with tail-window correction

Correction, 2026-09-21 (record 1802): the ``tailStart window`` conclusion
from record 1801 is withdrawn. Its Cartwright/Riemann--von Mangoldt cap was
an external paper-side heuristic, but it is not a constraint of the committed
owner constructor. The actual order is:

```text
choose tailStart from the tail budget
    -> set R = 2^(tailStart + 1) + 2 + dist(2, rho)
    -> for that arbitrary finite R construct correction and orbitIndex
       with square_zero_control and raw_square_tail.
```

The quantified theorem
`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets`
(`C1HealthyYoshidaUnscaledOrbit.lean:504-505`) is consumed verbatim by
`exists_orbitG8Geometry_of_sourceNontrivialZero_right`
(`C1G8R0OrbitGeometry.lean:169-178`). Therefore neither an ``empty window``
nor a width tension has been established. The gate measurements below remain
numerical evidence about their explicitly constructed surrogate family only.
They do not instantiate the constructor's full ball-zero and tail data.

Status: the producer's gate is anatomized at the surrogate-family level; the
former width-tension conclusion is withdrawn (2026-09-21).

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
- **The 1801b tail-window verdict is not route evidence**: it imposed a
  Cartwright cap absent from the formal constructor. It is retained only as
  a diagnostic of its surrogate family, not as a feasibility screen.
- **The remaining actual question**: can the constructor-selected correction,
  which already supplies every finite ball-zero and fourth-order-tail field,
  be shown to have `ICgate(g.convolutionSquare) <= 0`? This is the C3/B5
  signed estimate, unchanged in logical strength.

Next active target: an analytic readback of the actual constructor-selected
correction into the finite prime profile and `ICgate` budget. A numerical
surrogate may guide that work only after it represents the same finite
ball-zero and fourth-order-tail data. No committed-definition revision is
indicated by the withdrawn cap.
