# Record 3202: exact diagnostic-to-owner window decomposition

Record 3201 proves both outer weighted physical integrals vanish by support. This
record applies Mathlib's adjacent-interval identity twice and uses explicit
`IntervalIntegrable` assumptions for the left, inner, and right pieces.

It proves:

```text
integral[-diagnosticRadius, diagnosticRadius] weightedExternal
  = integral[-ownerRadius, ownerRadius] weightedExternal
```

The theorem does not manufacture interval integrability. Those three premises
remain visible in the theorem type and must later be supplied by the same
owner Taylor/cell chain. The result is therefore an exact decomposition bridge,
not a numerical certificate by itself.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAOwnerWindowDecomposition3202.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerWindowDecomposition3202Audit.lean`
- `build-logs/3202_wsl_build.log`
- `build-logs/3202_wsl_audit.log`

The audit uses only `[propext, Classical.choice, Quot.sound]`.