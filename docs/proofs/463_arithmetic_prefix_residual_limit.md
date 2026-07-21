# Proof 463: Arithmetic-prefix and residual limits

## Result

Proof 463 turns trace-class diagonal summability into an ordered prefix limit:

```text
Tr_prefix_N(operator) -> ordinaryTraceAlong(operator).
```

Applied to the actual finite-prime arithmetic operator, the limit is the
existing selected finite-prime sum:

```text
Tr_prefix_N(arithmeticOperator)
  -> sum_(p,m) finitePrimeTerm(p^m).
```

Combining this with Proof 462 gives the exact completed-residual limit

```text
completedResidual_prefix_N
  -> ordinaryTraceAlong(rootSandwichedBandResponse)
     - sum_(p,m) finitePrimeTerm(p^m).
```

The root-cycle defect remains inside `completedResidual_prefix_N`; no separate
trace or norm claim is made for it.

## Boundary

This closes the finite-prime prefix convergence bookkeeping.  It does not
prove a uniform bound or sign for the completed residual, nor Gate 3U, the
finite-S sign, negative-owner integration, Burnol's identity, or
`_root_.RiemannHypothesis`.
