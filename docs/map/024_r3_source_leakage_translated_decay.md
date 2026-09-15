# 024 — R3 source leakage translated pointwise decay

**Date:** 2026-09-15.

**Status:** formal pointwise source-owner brick; supporting route record, not
an RH claim.

**Consumer:** the healthy CompactLog, B5-shaped detector-specific statement
0 <= C1SameOwnerWeil.qw g.

## 1. Exact result

Record 1457 proves decay after the selected root for the doubled-shift
defect steps.  Record 1452 identifies the actual source leakage owner as a
translation conjugate of that rooted defect:

    sourceRootCompletedRightCommutatorLeftLeg
      = U_b * rootConvolution * (p_b - T_b) * U_(-b).

The new declaration

    sourceRootCompletedRightCommutatorLeftLeg_apply_translated_defect_step_norm_tendsto_zero

transports the 1457 pointwise result through this exact conjugation.  For
every selected owner, Sonin scale, and carrier vector v, the norm of the
actual source leakage applied to U_b * T_b^(n+1) v tends to zero.

The proof uses the inverse translation identity U_(-b) * U_b = I and the
isometry of global-log translation.  It adds no sign assumption and does not
replace the source owner by the abstract root owner.

## 2. Boundary

The result is still pointwise.  It gives no uniform decay rate, same-basis
square-summability, Hilbert--Schmidt estimate, trace-class estimate, or
cutoff/source transport.  In particular, bounded translation covariance
cannot turn pointwise convergence into the detector-weighted trace required
by the G8 readback.

The next live target is therefore a genuine energy or kernel theorem for the
translated source leakage, followed by the existing same-owner G8 transport.
The common-right leg remains controlled only in the signed paired corner of
record 1456.

## 3. Acceptance

Focused log:
/home/peter/rh/build-logs/1458_source_leakage_decay_try2.log

The focused build completed successfully (3285 jobs), with zero error lines,
zero sorryAx, and one audited declaration with axioms
[propext, Classical.choice, Quot.sound].

Unified acceptance:
/home/peter/rh/build-logs/1458_r1_unified_batch.log

The 32-target batch completed successfully (3317 jobs), with zero error
lines, zero sorryAx, and 113 Quot.sound] audit terminators.  The sole
diagnostic is the existing long-line linter warning on the audit print.
