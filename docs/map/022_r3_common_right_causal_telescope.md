# 022 — R3 common-right causal telescope

**Date:** 2026-09-15.

**Status:** formal structural brick plus signed paired trace bridge; supporting
route record, not an RH claim.

**Consumer:** the healthy-`CompactLog`, B5-shaped statement
`0 <= C1SameOwnerWeil.qw g` for the same tower-selected detector.

## 1. Exact result

For a visible-prime list `S`, the new leaf defines the finite operator
telescope

```text
T([]) = 0
T(p :: S) = M(S) * delta_p + T(S),
```

where `M(S)` is the normalized causal prefix and `delta_p` is the exact
one-prime translation coboundary.  Lean proves

```text
normalizedFiniteEulerInverseList S - I = T(S).
```

After specializing to the canonical finite-prime family, the source
root-completed common-right leg is exactly

```text
rootConvolution owner * sourceSoninProjection lambda
  * T(family.visiblePrimes) * sourceBandProjection lambda.
```

The source-side radial support projections and the identity mass have been
removed by proved projection identities; the finite visible-prime list is
retained explicitly.

The new 1456 bridge pairs this right leg with the left root and proves the
exact complete-corner identity

    (rootConvolution owner * sourceBandProjection lambda).adjoint
      * (rootConvolution owner * sourceSoninProjection lambda
          * T(family.visiblePrimes) * sourceBandProjection lambda).

The existing physical three-branch owner then supplies IsTraceClassAlong for
this paired operator under the source prolate square-sum hypothesis.  The
bridge is a signed trace interface: it does not assert that the common-right
leg by itself is Hilbert--Schmidt.

## 2. Boundary

This is an exact finite decomposition, not a trace estimate.  Finiteness of
the visible-prime list alone does not control the global carrier columns, and
the individual root-applied translation coboundaries are not yet shown
Hilbert--Schmidt.  The paired corner is now trace-class under the existing
physical factor hypothesis, but the theorem has not yet identified its limit
with the G8 cutoff ledger.  The next analytic targets are the leakage
root-side estimate and the cutoff/source transport needed for the same-owner
G8 readback.

## 3. Acceptance

The signed paired bridge acceptance is the focused log
1456_signed_common_right_try3.log: Build completed successfully (3299 jobs),
zero error lines, zero sorryAx, and two audited declarations with only
[propext, Classical.choice, Quot.sound].

Focused acceptance is `build-logs/1455_common_right_telescope_try2.log`:
`Build completed successfully (3285 jobs)`, zero `error:` lines, zero
`sorryAx`, and four audited declarations with only
`[propext, Classical.choice, Quot.sound]`.
