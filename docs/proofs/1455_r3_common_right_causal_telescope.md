# 1455 — R3 common-right causal telescope

**Date:** 2026-09-14.

**Classification:** FORMAL structural bridge; no sign, trace, or RH claim.

## Consumer and scope

This brick serves the same healthy-`CompactLog`, B5-shaped detector-specific
readback consumer `0 <= C1SameOwnerWeil.qw g`.  It packages the common-right
finite-Euler leg without changing the owner, visible-prime family, or source
carrier.

## Machine result

For a visible-prime list `S`, Lean defines

```text
T([]) = 0
T(p :: S) = M(S) * delta_p + T(S),
```

with `M(S)` the normalized causal prefix and `delta_p` the exact one-prime
translation coboundary.  It proves

```text
normalizedFiniteEulerInverseList S - I = T(S).
```

Using the canonical family/list identification and the centered causal
crossing identity, the actual common-right leg satisfies

```text
sourceRootCompletedCommonRightLeg owner lambda
  (E_lambda * normalizedFiniteEulerInverse family * E_lambda)
  = rootConvolution owner * sourceSoninProjection lambda
      * T(family.visiblePrimes) * sourceBandProjection lambda.
```

The proof is exact finite-list induction plus the previously proved source
projection identities.  No sign premise, health data, or RH statement is
used.

## Evidence

```text
/home/peter/rh/build-logs/1455_common_right_telescope_try2.log
Build completed successfully (3285 jobs).
error: 0
sorryAx: 0
Quot.sound] audit terminators: 4
```

The telescope exposes the next genuine estimate: control each root-applied
translation coboundary on the same global basis.  The decomposition itself
does not imply Hilbert--Schmidt or trace-classness.
