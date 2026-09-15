# 023 — R3 leakage root pointwise decay

**Date:** 2026-09-15.

**Status:** formal pointwise analytic brick; supporting route record, not an
RH claim.

**Consumer:** the healthy CompactLog, B5-shaped detector-specific statement
0 <= C1SameOwnerWeil.qw g.

## 1. Exact result

Record 1450 proves the actual no-gap strong limit

    T_b^n v -> r_b v

for every carrier vector.  Record 1454 identifies the doubled-shift defect
after the first step with the adjacent power difference

    (p_b - T_b) * T_b^(n+1)
      = T_b^(n+1) - T_b^(n+2).

The new declaration

    rootConvolution_apply_doubledShiftDefect_step_norm_tendsto_zero

combines these facts with continuity of the selected root and proves, for
every selected owner, scale coordinate b, and carrier vector v,

    ||rootConvolution owner
        ((p_b - T_b) * T_b^(n+1) v)|| -> 0.

This is the first root-side consequence of the no-gap limit on the actual
leakage normal form.  It uses no Weil sign, healthy-detector proposition,
SourceRH, or universal positivity premise.

## 2. Boundary

Pointwise decay is not a Hilbert--Schmidt square-sum and does not imply
trace-classness.  The root remains a bounded whole-line convolution
multiplier, and no uniform rate or basis summability is proved here.  The
next leakage target is a same-basis energy estimate for these defect steps,
or a signed kernel/commutator estimate that upgrades the pointwise decay to
the trace owner used by the G8 readback.

The common-right telescope is already paired with the complete corner by
record 1456.  The cutoff/source transport and the final G8 readback remain
open.

## 3. Acceptance

Focused log:
/home/peter/rh/build-logs/1457_leakage_pointwise_try4.log

Build completed successfully (3284 jobs), zero error lines, zero sorryAx, and
one audited declaration with axioms
[propext, Classical.choice, Quot.sound].

The unified 30-target R3 batch also passed:
1457_r1_unified_batch.log, Build completed successfully (3315 jobs), zero
error lines, zero sorryAx, and 112 Quot.sound] audit terminators.
