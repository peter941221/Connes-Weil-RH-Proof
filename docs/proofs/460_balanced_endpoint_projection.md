# Proof 460: Balanced endpoint projection ledger

## Result

Proof 460 rewrites the Proof 459 source-Gram plus tail-boundary owner using the
exact complement identity `P_N + (I-P_N) = I`.  The base terms become

```text
source side: base† P_global base
target side: base (I-P_source) base†
```

and the dual/frame terms are paired in the same way:

```text
source side: frame† P_global dual
target side: dual (I-P_source) frame†.
```

The resulting `actualBandEndpointBalancedPrefixTrace` is proved equal to the
source-Gram plus endpoint-tail scalar, and therefore to

```text
2 * integral_0^1 weightedBoundaryTrace(alpha) d alpha.
```

No source or target tail is estimated independently.

## Boundary

The balanced projection form exposes the complementary source/target split
needed for a Schur or Bessel estimate, but it is still an exact ledger.  The
uniform paired bound, Gate 3U, finite-S sign, negative-owner integration,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.
