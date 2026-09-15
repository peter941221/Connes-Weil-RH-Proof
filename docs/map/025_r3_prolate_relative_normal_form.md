# 025 — R3 prolate relative-motion normal form

**Date:** 2026-09-15.

**Status:** formal structural/ideal-transfer brick; supporting route record,
not an RH claim.

**Consumer:** the healthy CompactLog, B5-shaped detector-specific statement
`0 <= C1SameOwnerWeil.qw g`.

## 1. Exact result

The moving source factor is not a copy of the unit-scale factor.  The radial
and Fourier projections move in opposite directions, so the correct object
is the relative-motion factor

    doubledShiftProlateHilbertSchmidtFactor b
      = Q_0 * (p_b - r_b),

where `p_b` is the doubled-shift radial projection and `r_b` is the
doubled-shift Sonin intersection projection.  The new formal identity is

    sourceProlateHilbertSchmidtFactor lambda
      = U_b * doubledShiftProlateHilbertSchmidtFactor (log lambda) * U_(-b),

with `b = log lambda`.  The proof consumes the exact source Fourier scale
conjugacy, the doubled-shift radial transport, and the source Sonin
projection transport.

## 2. Ideal consequence

Bounded precomposition and postcomposition by the global-log translations
give the named-basis equivalence

    source factor square-summable
      iff relative-motion factor square-summable.

This is a genuine reduction of the moving-scale HS obligation.  It does not
claim that the relative-motion factor is HS, does not transfer the unit-scale
strict-angle theorem to arbitrary `b`, and does not prove the detector-
weighted trace or G8 readback.

## 3. Remaining boundary

The next analytic target is now explicit: prove a same-basis square-sum or an
equivalent positive trace bound for `Q_0 * (p_b - r_b)` at the detector-selected
scales, uniformly enough for the healthy owner.  The already-proved unit
scale factor theorem supplies only `b = 0`; it cannot be reused as a blanket
moving-scale certificate.  The leakage pointwise decay of records 1457--1458
and the signed common-right corner of 1456 remain separate consumers until
this relative-motion energy is available.

## 4. Acceptance

Focused log:

    /home/peter/rh/build-logs/1459_r3_prolate_relative_try3.log

The focused build completed successfully (3282 jobs), with zero error lines,
zero `sorryAx`, and seven audited declarations, all with the standard axiom
set `[propext, Classical.choice, Quot.sound]`.

Unified route batch:

    /home/peter/rh/build-logs/1459_r1_unified_batch.log

The 34-target batch completed successfully (3319 jobs), with zero error
lines, zero `sorryAx`, and 120 `Quot.sound]` audit terminators.  The only
diagnostics are existing `simpa`/long-line linter warnings.

Lean leaves:

    ConnesWeilRH/Dev/C1G8R3ProlateRelativeNormalForm.lean
    ConnesWeilRH/Dev/C1G8R3ProlateRelativeNormalFormAudit.lean
