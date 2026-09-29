# Record 2174: coefficient-scaled four-point tail contract

Date: 2026-09-29

## Consumer and owner

The consumer is the healthy `CompactLog` same-owner contradiction route:
the selected span must have a nonpositive semi-local gate and a strictly
negative `qw`.  The owner remains the exact
`annihilatorDetectorSpanVector (fullFunctionalEquationOrbitAnnihilator g rho)
g lambda`; no fixed-prime or continuous owner is substituted.

## Result

`C1FourPointContradictionAssembly.lean` adds
`qw_neg_of_spectralHeightShellPrefix_and_coefficient_scaled_tail`.
It consumes a fourth-order tail certificate at the matching scale
`epsilon = lambda * eta` and a transported prefix
`prefix <= -xiMultiplicity(rho) * lambda^2`.  From `0 < lambda`, the proof
factors the tail bound as

```text
4 (lambda eta)^2 C (3/4)^N
  = lambda^2 [4 eta^2 C (3/4)^N]
```

and cancels the positive `lambda^2`.  The remaining acceptance premise is
the coefficient-independent budget
`4 eta^2 C (3/4)^N < xiMultiplicity(rho)`.

This strictly shrinks the named quantitative obligation: the gate-selected
coefficient no longer appears in the tail margin.  It does not prove the
matching scaled tail, the gate, or RH.  Those remain the producer obligations.

## Verification

- Module: `ConnesWeilRH/Dev/C1FourPointContradictionAssembly.lean`.
- Paired audit: `ConnesWeilRH/Dev/C1FourPointContradictionAssemblyAudit.lean`.
- WSL module build: `results/20260929_coeff_scaled_tail_module_build5.log`;
  footer `Build completed successfully`, 3813 jobs, no `error:`.
- WSL audit build: `results/20260929_coeff_scaled_tail_audit_build7.log`;
  zero `error:` and the new theorem's axioms are exactly
  `[propext, Classical.choice, Quot.sound]`.

No RH claim is made.  The route status and owner quantifiers are unchanged.
