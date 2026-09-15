# 1456 — R3 signed common-right trace bridge

**Date:** 2026-09-15

**Status:** formal GREEN; supporting route record, not an RH claim
**Consumer:** the healthy CompactLog, B5-shaped same-owner statement
0 <= C1SameOwnerWeil.qw g

## Result

The 1455 finite visible-prime coboundary telescope is an exact right-leg
identity.  The new Dev leaf C1G8R3SignedCommonRightTrace.lean pairs it with
the left root and proves the exact complete-corner identity:

    sourceRootCompletedFixedQuotientCorner owner lambda
      (radialSupportProjection lambda * normalizedFiniteEulerInverse family
        * radialSupportProjection lambda)
    =
    (rootConvolution owner * sourceBandProjection lambda).adjoint
      * (rootConvolution owner * sourceSoninProjection lambda
          * telescope(family.visiblePrimes) * sourceBandProjection lambda)

The source physical three-branch owner already proves IsTraceClassAlong for
the complete finite-Euler corner under the named support, basis, and prolate
square-sum hypotheses.  Rewriting by the new paired identity therefore proves
trace-classness for the explicitly telescoped paired operator.

The audited declarations are:

    sourceRootCompletedFiniteEulerCorner_eq_coboundaryPaired
    sourceRootCompletedFiniteEulerCorner_coboundaryPaired_isTraceClassAlong

## Why this is the right interface

The old possible target was an individual Hilbert--Schmidt estimate for the
common-right leg.  The existing source trace theory does not own that
single-leg operator; it owns the signed, detector-coupled corner.  The new
bridge makes this distinction formal instead of silently treating a finite
prime list as global smoothing.

Thus the 1456 result is a real route reduction:

    finite prime telescope
      -> exact signed paired corner
      -> existing physical trace-class owner

It does not prove that the common-right leg alone is Hilbert--Schmidt, and it
does not identify the trace with the G8 cutoff ledger.

## Remaining boundary

The live R3 obligations are now:

1. prove the root-side trace/energy estimate for the leakage leg, or a
   compatible signed estimate that consumes the doubled-shift defect;
2. prove cutoff/source transport for the same canonical owner and basis;
3. identify the resulting paired trace with G8SameOwnerReadbackData;
4. apply the already formal same-detector contradiction and SourceRH wrapper.

No Weil sign, healthy-detector proposition, SourceRH, or universal
positivity premise is used in this brick.

## Acceptance

Focused log:
/home/peter/rh/build-logs/1456_signed_common_right_try3.log

The unified R3 Dev batch also passed in
/home/peter/rh/build-logs/1456_r1_unified_batch.log:
Build completed successfully (3313 jobs), zero error lines, zero sorryAx, and
111 Quot.sound] audit terminators.

Evidence:

    Build completed successfully (3299 jobs)
    error lines: 0
    sorryAx lines: 0
    audited declarations: 2
    axioms: [propext, Classical.choice, Quot.sound]

RH is not claimed.
