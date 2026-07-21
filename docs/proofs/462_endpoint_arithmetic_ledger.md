# Proof 462: Endpoint arithmetic ledger

## Result

Proof 462 cycles the right convolution root in Proof 461's finite target
prefix.  The cycle is finite-dimensional and retains its exact prefix defect:

```text
Tr_prefix(C (R_0-R_S) C^dagger)
  = Tr_prefix((C^dagger C) (R_0-R_S))
    + rootCycleDefect_prefix.
```

The cycled operator is the existing `projectionResponse`.  Expanding its
same-object definition gives

```text
Tr_prefix(rootSandwichedBandResponse)
  = Tr_prefix(arithmeticOperator)
    + completedResidual_prefix,

completedResidual_prefix
  = Tr_prefix(sameObjectResidual) + rootCycleDefect_prefix.
```

Combining this with Proof 461 identifies twice the complete weighted boundary
integral with the same arithmetic-plus-completed-residual ledger.  The root
cycle defect is not discarded or estimated independently.

## Boundary

The finite arithmetic prefix has not yet been replaced by its ordinary trace,
and the completed residual has no uniform sign or bound.  Gate 3U, the
finite-S sign, negative-owner integration, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
