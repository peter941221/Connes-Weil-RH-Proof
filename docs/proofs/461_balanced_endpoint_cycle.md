# Proof 461: Exact balanced endpoint cycle

## Result

Proof 461 performs the balanced source/target ledger cycle entirely in the
finite rectangular matrices.  For arbitrary Hilbert bases, source and target
prefix sizes, and rectangular maps `A` and `B`, Lean proves

```text
Tr_source(B P_target A)
  + Tr_target(A (I-P_source) B)
  = Tr_target(A B).
```

The cancellation is the finite identity
`Tr(M_B M_A) = Tr(M_A M_B)` for the two rectangular prefix matrices.  It does
not use an infinite-dimensional trace cycle.

Specializing `A` and `B` to the actual base and dual/frame root legs gives

```text
actualBandEndpointBalancedPrefixTrace
  = Re Tr_targetPrefix(rootSandwichedBandResponse).
```

The source cutoff is therefore an internal ledger parameter and disappears
from the exact target-prefix response.  Combining this with Proof 460 gives
the direct endpoint identity

```text
Re Tr_targetPrefix(rootSandwichedBandResponse)
  = 2 * integral_0^1 weightedBoundaryTrace(alpha) d alpha.
```

## Boundary

This removes the source/target carrier bookkeeping from the balanced endpoint
owner, but it is still an identity rather than a uniform estimate.  The
target-prefix response bound, Gate 3U, finite-S sign, negative-owner
integration, Burnol's identity, and `_root_.RiemannHypothesis` remain open.
