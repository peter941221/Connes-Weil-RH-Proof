# Record 2583: analytic-owner membership bridge

Date: 2026-10-05

Status: FORMAL-INTERFACE-PASS pending the external component residual.

This record closes the interface between the existing analytic moment system
and the 2570 correction boxes. `actualCorrectionOwner2351` is the existing
unique solution of the 30 by 30 `ownerMomentMatrix2351`; its Laplace-node
realization is reproved through the existing determinant premise. A separate
theorem converts the two componentwise midpoint-distance bounds into
`ComplexRect2427.Mem` for each correction box.

The componentwise distance premise is deliberately explicit. It is the exact
remaining shape needed from the 2338 directed residual transfer. No external
float or Arb result is imported as a Lean fact here.

## Boundary

This record does not prove the componentwise residual, exact coefficient
membership, producer GO, or RH. The next certificate must provide those two
real-coordinate bounds for the same `modulations`, `nodes`, and `target` that
define the live owner.

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionMembershipBridge2583.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionMembershipBridge2583Audit.lean`
- `ConnesWeilRH/Dev/C1RouteAAnalyticMomentSystem.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionCenterNode2570.lean`
