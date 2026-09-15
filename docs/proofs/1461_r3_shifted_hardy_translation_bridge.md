# 1461 — R3 shifted Hardy translation bridge

**Date:** 2026-09-15

**Consumer:** healthy CompactLog, B5-shaped detector-specific
`0 <= C1SameOwnerWeil.qw g`.

## Result

The previously open translation bridge is now formal:

    T_(2b) * doubledShiftRawSupportCrossing b * T_(-2b)
      = doubledShiftHardyRawSupportCrossing b.

The proof does not expand the full operator expression at once.  It proves
the two translation inverse laws on vectors, transports the radial projection,
uses the unit Fourier-support/Hardy conjugacy, and then rewrites the crossing
pointwise.  This avoids the deterministic kernel timeout encountered by the
earlier operator-level normalization.

Together with record 1460, the relative defect is therefore formally reduced
to the shifted negative Hardy window

    -M * K_b * M * K_b * P.

## Boundary

This closes only the coordinate/transport bridge.  It does not prove the
relative-factor Hilbert--Schmidt or positive-trace estimate, the same-basis
energy upgrade, G8 cutoff/source transport, detector-specific `qw >= 0`, or
RH.

## Acceptance

    /home/peter/rh/build-logs/1461_formal_bridge_audit_try3.log

`Build completed successfully (3283 jobs)`, zero error lines, zero `sorryAx`,
and five audit `Quot.sound]` terminators.  The new theorem prints only
`[propext, Classical.choice, Quot.sound]`.

No numerical experiment or untrusted axiom was used.
