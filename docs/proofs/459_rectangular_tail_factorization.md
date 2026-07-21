# Proof 459: Rectangular boundary tail factorization

## Result

Proof 459 constructs the finite-rank projection onto the first `N` vectors of
a natural Hilbert basis:

```text
P_N = sum_(k<N) rankOne(b_k,b_k).
```

It proves that multiplying two rectangular prefix matrices inserts exactly
this projection on the intermediate carrier:

```text
M_N(A) M_N(B) = M_N(A P_N B).
```

Consequently, the target and source product defects from Proof 456 are genuine
complementary-tail compressions:

```text
targetDefect = M_target(A (I-P_source) B),
sourceDefect = M_source(B (I-P_target) A).
```

No infinite trace cycle or limiting argument is used.

## Endpoint specialization

Proof 458's two-cycle endpoint boundary is rewritten as the difference of the
base/base-adjoint tail cycle and the dual/frame-adjoint tail cycle.  Therefore
the active identity becomes

```text
Tr M_source(sourceBandGramResponse)
  + endpointTailBoundary
  = 2 * integral_0^1 weightedBoundaryTrace(alpha) d alpha.
```

The new canonical consumer accepts one bound on this complete source-Gram plus
tail-boundary scalar.  It does not permit separate absolute estimates of the
four tail compressions.

## Boundary

Proof 459 exposes the actual tail operators but does not bound them uniformly.
The remaining analytic problem is to exploit the paired base/dual geometry and
the source Gram term before taking an absolute value.  Gate 3U, the finite-S
sign, negative-owner integration, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
