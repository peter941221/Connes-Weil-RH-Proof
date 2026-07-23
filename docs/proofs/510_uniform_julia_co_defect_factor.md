# Proof 510: family-uniform Julia co-defect factor handoff

## Result

Proof 510 connects the family contract from Proof 509 to the local signed
trace owner. Given one common physical domination bound for every visible
prime and suffix, it constructs a genuine family of local Douglas factors:

```text
LocalMismatch(p,S)
  = LeftJuliaCoDefect(p,S) * RightFactor(p,S)
||RightFactor(p,S)|| <= bound.
```

It also preserves the exact zero-mode consequence: the adjoint local mismatch
vanishes on the kernel of the adjacent Julia co-defect.

This is a producer handoff, not the producer itself. The source-specific
physical domination remains open. No trace estimate, Gate 3U sign, Burnol
identity, or RH premise is introduced.

## Directionality guard

The construction is intentionally one-way. A local factor family does not
automatically recover physical domination: the reverse readback uses the
scalar-normalized forward Euler transition, whose norm is not available as a
uniform contraction. Promoting the factor family back to the physical bound
would therefore be an unproved strengthening.

## Lean owner and audit

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaUniformCoDefectFactor.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaUniformCoDefectFactorAudit.lean
```

The audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`. The finite-S sign, Burnol identity,
and unconditional RH remain open.
