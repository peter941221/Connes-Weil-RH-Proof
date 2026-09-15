# 1460 — R3 relative defect crossing

**Date:** 2026-09-15

**Consumer:** healthy CompactLog, B5-shaped detector-specific
`0 <= C1SameOwnerWeil.qw g`.

## Result

Added the paired Dev/Audit leaves

    ConnesWeilRH/Dev/C1G8R3RelativeDefectCrossing.lean
    ConnesWeilRH/Dev/C1G8R3RelativeDefectCrossingAudit.lean

The new exact cancellation is

    doubledShiftProlateDefectFactor b
      = doubledShiftRawSupportCrossing b,

where the right side is the raw crossing `(1 - p_b) * Q_0 * p_b`.
The proof uses the two projection absorption identities for the genuine
intersection range on the same finite-S carrier.

The leaf also records the independently useful coordinate facts

    T_(2b) * p_b * T_(-2b) = P,
    Q_0 = H * P * H,

and proves the shifted-window identity from the Hardy involution:

    M * K_b * P * K_b * P = -M * K_b * M * K_b * P.

The latter is proved through a generic ring lemma and instantiated once in
the continuous-linear-map operator ring.  This avoids a kernel-timeout caused
by expanding the same algebra directly at the large operator type.

## Boundary

The full translation bridge from the raw support crossing to the shifted
Hardy crossing remains open.  It is kept as a named target but is not claimed
by this record.  In particular, this brick supplies no relative-factor
Hilbert--Schmidt estimate, positive trace, G8 readback, R3 positivity, or RH
conclusion.

This was the boundary at record 1460.  The transport bridge was subsequently
closed by the vector-level proof in record 1461; the analytic HS/trace
boundary remains unchanged.

## Acceptance

Owning module:

    /home/peter/rh/build-logs/1460_relative_defect_try15.log

`Build completed successfully (3282 jobs)`, zero error lines, and zero
`sorryAx`.

Owning module plus paired audit:

    /home/peter/rh/build-logs/1460_relative_defect_try16_audit.log

`Build completed successfully (3283 jobs)`, zero error lines, zero `sorryAx`,
and four `Quot.sound]` occurrences matching the four `#print axioms` lines.
The audited declarations print only `[propext, Classical.choice, Quot.sound]`.

No numerical experiment or untrusted axiom was used.
