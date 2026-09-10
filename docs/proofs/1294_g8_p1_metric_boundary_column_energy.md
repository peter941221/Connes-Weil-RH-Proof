# G8 P1 metric-boundary column energy (2026-09-11)

## Result

`C1G8P1BoundaryColumnEnergy` proves an unconditional square-energy estimate for
the literal finite-Euler metric boundary column.  For every visible-prime list
`S` and source vector `x`,

```text
‖finiteEulerMetricBoundaryColumn λ S x‖²
  ≤ juliaDefectEnergy (suffixEulerFrameSchurSteps λ S) x
  ≤ ‖x‖².
```

The proof unfolds the ordered metric boundary-output recursion.  The remaining
ambient adjoint suffix is contractive, each rectangular boundary dagger is
bounded by its local Julia defect, and the tail is pulled back by the adjoint
source transition.  The final column identity is the finite `PiLp` L² norm
formula.

## Scope and gap

This is a P1 quantitative bound on the metric owner only.  It does **not** say
that a metric boundary output is a radial Sonin crossing, does not produce a
finite prime-power trace, and does not supply the remainder-to-zero or cutoff
trace limit required by `G8SameOwnerReadbackData`.  The typed metric-to-radial
transport remains an explicit producer obligation (record 1292).

## Evidence

- Lean leaf: `ConnesWeilRH/Dev/C1G8P1BoundaryColumnEnergy.lean`
- Audit leaf: `ConnesWeilRH/Dev/C1G8P1BoundaryColumnEnergyAudit.lean`
- Build log: `/home/peter/rh/build-logs/1347_g8_p1_boundary_energy.log`
- Acceptance: `Build completed successfully (3464 jobs)`; no `error:` or `sorryAx` lines.
- Audit declarations use only `[propext, Classical.choice, Quot.sound]`.

Status: **formal, consumer-side P1 bound; producer transport still open**.
