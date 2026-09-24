# 1921 — Same-owner four-point gate polarization

Date: 2026-09-24.

Status: FORMAL algebraic infrastructure. This record does not prove the
selected-detector determinant sign and does not change the route ruling.

## Result

`C1FourPointSpanGateCertificate.lean` now proves, for the actual
annihilator-detector pair `u, g` and one common support owner, that the two
symmetric span evaluations recover the directed cross-gate sum:

```text
2 * (B01 + B10) = Q(-1) - Q(1).
```

It also proves the exact equivalent form of the vertex determinant:

```text
D*C - ((B01+B10)/2)^2
  = D*C - ((Q(-1)-Q(1))/4)^2.
```

The statements are `annihilator_span_gate_polarization` and
`annihilator_span_gate_det_eq_symmetric_gap`. They use the existing exact
same-owner parabola and introduce no cross-term symmetry assumption.

## Verification

Focused WSL build log: `20260924_fourpoint_polarization2.log`.

The owning module and paired audit both built successfully (3809 jobs, zero
`error:` lines). The audit prints the two declarations with only the standard
axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs.

## Route effect

This removes a manual cross-term expansion from the next selected-owner
estimate and gives an exact gate-value readback for channel decomposition. It
is not a strict sign margin: the determinant inequality and the Cut-1 joint
tail margin remain open in map 103.
