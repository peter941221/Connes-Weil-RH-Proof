# 1458 — R3 source leakage translated pointwise decay

**Date:** 2026-09-15

**Consumer:** healthy CompactLog, B5-shaped detector-specific
0 <= C1SameOwnerWeil.qw g.

## Result

Added the paired Dev/Audit leaves

    ConnesWeilRH/Dev/C1G8R3SourceLeakageTranslatedDecay.lean
    ConnesWeilRH/Dev/C1G8R3SourceLeakageTranslatedDecayAudit.lean

The theorem

    sourceRootCompletedRightCommutatorLeftLeg_apply_translated_defect_step_norm_tendsto_zero

states that, for every selected Weil-square owner, scale lambda, and carrier
vector v, the actual source leakage applied to the translated alternating
power step has norm tending to zero:

    || sourceLeakage(lambda) (U_log(lambda) (T_log(lambda)^(n+1) v)) ||
      -> 0.

## Proof mechanism

The exact source leakage normal form from record 1452 is used as an operator
identity.  The inverse global-log translations cancel, leaving the root
applied to the doubled-shift defect.  Record 1457 supplies its pointwise
decay, while the global-log translation is an isometry.  A squeeze argument
then returns the statement to the actual source leakage owner.

## Boundary

This is not a square-sum, Hilbert--Schmidt, trace-class, positivity, or Weil
sign theorem.  Pointwise convergence alone does not close the detector
weighted trace.  The remaining source-side obligation is a same-basis
energy/kernel estimate for these translated steps, followed by cutoff/source
transport into the G8 same-owner readback.  RH is not claimed.

## Acceptance

Focused acceptance:

    /home/peter/rh/build-logs/1458_source_leakage_decay_try2.log

Build completed successfully (3285 jobs), with zero error lines and zero
sorryAx.  The paired audit prints one standard axiom set:

    [propext, Classical.choice, Quot.sound]

Unified acceptance:

    /home/peter/rh/build-logs/1458_r1_unified_batch.log

The 32-target batch completed successfully (3317 jobs), with zero error
lines, zero sorryAx, and 113 Quot.sound] audit terminators.
