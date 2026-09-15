# 1457 — R3 leakage root pointwise decay

**Date:** 2026-09-15

**Status:** formal GREEN; supporting route record, not an RH claim
**Consumer:** the healthy CompactLog, B5-shaped detector-specific statement
0 <= C1SameOwnerWeil.qw g

## Machine result

The new Dev leaf
C1G8R3LeakageRootPointwiseDecay.lean combines the no-gap power limit from
1450 with the defect telescoping identity from 1454.

For every selected owner, real parameter b, and carrier vector v, it proves

    ||rootConvolution owner
        ((doubledShiftRadialProjection b
          - doubledShiftAlternatingProduct b)
          * doubledShiftAlternatingProduct b^(n+1) v)||
      -> 0.

The proof takes the two shifted limits

    T_b^(n+1) v -> r_b v
    T_b^(n+2) v -> r_b v

subtracts them, applies the continuous selected root, and rewrites the
result with the exact 1454 applied-vector identity.

## What this closes

The moving leakage normal form now has a proved root-side pointwise decay
consumer.  In particular, the defect is not merely an unnamed bounded
difference: after the selected root, every adjacent alternating-power step
vanishes on every carrier vector.

## What it does not close

This is not a Hilbert--Schmidt square-sum, a trace-class theorem, or a
uniform rate.  Pointwise decay alone cannot justify the same-basis trace
limit.  The next required analytic brick is a basis-compatible energy or
kernel estimate upgrading this decay, while preserving the same owner and
G8 source/cutoff interface.  The 1456 paired common-right trace bridge is
independent and remains available.

No Weil sign, healthy-detector proposition, SourceRH, or universal positivity
premise is used.

## Acceptance

Focused log:
/home/peter/rh/build-logs/1457_leakage_pointwise_try4.log

The unified 30-target R3 batch also passed in
/home/peter/rh/build-logs/1457_r1_unified_batch.log:
Build completed successfully (3315 jobs), zero error lines, zero sorryAx, and
112 Quot.sound] audit terminators.

    Build completed successfully (3284 jobs)
    error lines: 0
    sorryAx lines: 0
    audited declarations: 1
    axioms: [propext, Classical.choice, Quot.sound]

RH is not claimed.
