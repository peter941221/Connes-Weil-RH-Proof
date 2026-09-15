# 026 — R3 relative defect crossing

**Date:** 2026-09-15.

**Status:** formal structural brick; supporting route record, not an RH claim.

**Consumer:** the healthy CompactLog, B5-shaped detector-specific statement
`0 <= C1SameOwnerWeil.qw g`.

## 1. Exact result

For the relative prolate factor from record 1459, let `p_b` be the
doubled-shift radial projection, `r_b` the doubled-shift Sonin intersection
projection, and `Q_0` the unit Fourier-support projection.  The new leaf
defines the defect factor and proves the exact cancellation

    (1 - (p_b - r_b)) * (Q_0 * (p_b - r_b))
      = (1 - p_b) * Q_0 * p_b.

Thus the moving-scale prolate defect is an explicit raw support crossing.  No
angle gap, smoothing estimate, or numerical premise is used.

## 2. Shifted Hardy window

The leaf also formalizes the radial conjugacy by the translation `T_(2b)`
and the unit Fourier-support/Hardy conjugacy.  Independently, with

    K_b = T_(2b) * H,
    P   = positive-half-line projection,
    M   = 1 - P,

the involution `K_b * K_b = 1` and `M * P = 0` imply the exact operator
identity

    M * K_b * P * K_b * P = -M * K_b * M * K_b * P.

This is the signed shifted-window form that the relative crossing should
consume.  The formal translation bridge is now also proved:

    T_(2b) * ((1 - p_b) * Q_0 * p_b) * T_(-2b)
      = M * K_b * P * K_b * P
      = -M * K_b * M * K_b * P.

The proof is carried out by vector-level rewriting, rather than by asking the
kernel to normalize the whole composite operator at once.

## 3. Boundary

The translation bridge is formal, but it supplies no
Hilbert--Schmidt or positive-trace estimate for the relative factor.  The
same-basis energy upgrade, G8 cutoff/source transport, R3 positivity, and RH
remain open.

## 4. Acceptance

Focused acceptance:

    /home/peter/rh/build-logs/1460_relative_defect_try15.log

The owning module completed successfully (3282 jobs), with zero error lines
and zero `sorryAx`.

Paired audit acceptance:

    /home/peter/rh/build-logs/1460_relative_defect_try16_audit.log

The module plus audit completed successfully (3283 jobs), with zero error
lines, zero `sorryAx`, and four `Quot.sound]` audit terminators for four
printed declarations.  Each audited declaration has only
`[propext, Classical.choice, Quot.sound]`.

Bridge acceptance:

    /home/peter/rh/build-logs/1461_formal_bridge_audit_try3.log

The module plus paired audit completed successfully (3283 jobs), with zero
error lines, zero `sorryAx`, and five `Quot.sound]` audit terminators.  The
new bridge theorem also has only `[propext, Classical.choice, Quot.sound]`.

## 5. Lean leaves

    ConnesWeilRH/Dev/C1G8R3RelativeDefectCrossing.lean
    ConnesWeilRH/Dev/C1G8R3RelativeDefectCrossingAudit.lean
