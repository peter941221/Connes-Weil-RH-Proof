# 1459 — R3 prolate relative-motion normal form

**Date:** 2026-09-15

**Consumer:** healthy CompactLog, B5-shaped detector-specific
`0 <= C1SameOwnerWeil.qw g`.

## Result

Added the paired Dev/Audit leaves

    ConnesWeilRH/Dev/C1G8R3ProlateRelativeNormalForm.lean
    ConnesWeilRH/Dev/C1G8R3ProlateRelativeNormalFormAudit.lean

The new operator is

    doubledShiftProlateHilbertSchmidtFactor b = Q_0 * (p_b - r_b).

The main identity is

    sourceProlateHilbertSchmidtFactor lambda
      = U_log(lambda) * doubledShiftProlateHilbertSchmidtFactor (log lambda)
          * U_(-log(lambda)).

The proof uses exact projection transport and translation cancellation on the
same finite-S carrier.  No numerical premise is used.

## Ideal transfer

The paired summability lemmas apply the existing bounded precomposition and
postcomposition Hilbert--Schmidt ideal calculus in both directions.  For
every named Hilbert basis and every Sonin scale, source-factor square
summability is equivalent to relative-motion-factor square summability.

## Boundary

This closes the coordinate/transport ambiguity, not the analytic estimate.
The relative factor at nonzero `b` still needs a real square-sum or positive
trace estimate.  The unit-scale strict-angle result only covers `b = 0`.
No source leakage HS estimate, detector-weighted trace, G8 readback, R3
positivity, or RH conclusion is asserted.

## Acceptance

Focused acceptance:

    /home/peter/rh/build-logs/1459_r3_prolate_relative_try3.log

Build completed successfully (3282 jobs), zero error lines, and zero
`sorryAx`.  The seven audited declarations print only

    [propext, Classical.choice, Quot.sound]

Unified acceptance:

    /home/peter/rh/build-logs/1459_r1_unified_batch.log

The 34-target route batch completed successfully (3319 jobs), with zero
error lines, zero `sorryAx`, and 120 `Quot.sound]` audit terminators.  The
remaining diagnostics are existing linter warnings only.
