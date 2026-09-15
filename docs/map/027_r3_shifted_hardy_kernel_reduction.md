# 027 — R3 shifted Hardy kernel reduction

**Date:** 2026-09-15.

**Status:** formal conditional interface; supporting route record, not an RH
claim.

**Consumer:** the healthy CompactLog, B5-shaped detector-specific statement
`0 <= C1SameOwnerWeil.qw g`.

## Exact formal reduction

For `M = 1 - P`, where `P` is the fixed positive-half-line projection, and
`K_b = T_(2b) * H`, the new leaf defines the compact-window interior operator

    Interior_b = M * K_b * M.

The shifted raw crossing is exactly

    shiftedRaw_b = -Interior_b * K_b * P.

Therefore square-summability of the interior columns transfers to the shifted
raw crossing by bounded postcomposition.  The previously proved translation
bridge then gives the inverse conjugacy

    raw_b = T_(-2b) * shiftedRaw_b * T_(2b),

so square-summability transfers back to the original relative defect.

## Relative-factor closure interface

The leaf also proves the exact defect identity for the relative prolate factor
`A_b = Q_0 * (p_b - r_b)` and its defect `D_b`:

    D_b* D_b = A_b* A_b - (A_b* A_b)* (A_b* A_b).

Consequently, the existing strict-contraction Hilbert--Schmidt lemma gives

    strict_angle(A_b) + HS(Interior_b)
      -> HS(A_b).

This is a genuine interface theorem: it consumes only the named compact-window
compression square-sum and a strict norm bound.  It does not assume either
input.

In addition, the expected scaled additive Fourier kernel is defined as a
continuous kernel and its compact-interval operator is formally
Hilbert--Schmidt.  The actual literal operator is now identified with this
model on the full healthy even additive carrier.  The extension proceeds
through interval density and the projection image, not density in the
unprojected global L2.

The zero-scale anchor is now formal: `Interior_0` is exactly the existing
`unitInteriorFourierCompression`, and its basis square-sum follows from the
already accepted unit additive finite-window factor.  Thus the model constants
and carrier normalization agree with the actual owner at `b = 0`; this is an
anchor, not a general-scale identification.

The general carrier transport is also formal: the induced additive dilation
`doubledShiftEvenAdditiveDilation b` carries `Interior_b` to the literal
additive-even operator

    unitLiteralProjection * dilation_b * additiveFourier * unitLiteralProjection.

The dilation leg is now also read back exactly on the bundled even-Schwartz
core: it sends the bundled input to the bundled Schwartz function obtained by
multiplication by `exp b` and argument dilation by `exp (2*b)`.  Consequently
no further Mellin-coordinate or support-owner transport is hidden in the
remaining compact theorem.

The compact model side is now formal on the Schwartz core: the scaled Fourier
coefficient is exactly the model kernel coefficient, and the corresponding
compact interval operator equals restriction of the scaled Fourier transform
on the core product.  The actual literal operator is now identified with that
model operator on the full carrier by the interval density and projection-image
extension described above.

The actual shifted relative prolate factor is also formally unitarily
conjugate to the standard `prolateFactor` for
`doubledShiftHardyTranslationEquiv b`; the conjugating coordinate map is the
Hardy involution followed by the exact translation.  Its operator norm is
therefore exactly the norm of that standard factor.  This normalizes the
strict-angle question to the standard model at the translated parameter; it
does not prove the required strict inequality.

## Remaining boundary

The compact-kernel square-sum and its transfer to the actual additive and
shifted-Hardy interior compressions are formal.  The remaining independent
analytic brick is the strict norm bound for the relative prolate factor at
every selected detector scale, now reduced by exact unitary conjugacy to the
standard-model formulation.  Positive trace, same-basis G8 readback, the R3
detector sign, and RH remain open.

## Acceptance

    /home/peter/rh/build-logs/1477_conjugation_main_audit_try1.log

The updated module plus paired audit completed successfully with 3284 jobs,
zero error lines, zero `sorryAx`, and fifty-four `Quot.sound]` audit
terminators.  The new audited declarations include the shifted-factor
conjugacy and exact operator-norm equality.  Every audited declaration has
only `[propext, Classical.choice, Quot.sound]`.

    /home/peter/rh/build-logs/1475_hs_transfer_audit_try1.log

The 1475 module plus paired audit completed successfully with 3284 jobs,
zero error lines, zero `sorryAx`, and forty `Quot.sound]` audit terminators.
The new audited declarations include the interval zero-extension/evenization
density bridge, the actual literal/model equality on the full carrier, and the
model-to-actual Hilbert--Schmidt square-sum transfer, in addition to the exact
bundled even-Schwartz dilation readback, scaled Schwartz core, and compact
interval operator readback.  The preceding additive-transport
acceptance is retained in
`1464_additive_transport_audit_try7.log`; the zero-scale anchor acceptance is
retained in
`1463_zero_anchor_try4.log`, and the full reduction acceptance in
`1462_shifted_hardy_formal_audit_try7.log`.
Every audited declaration has only `[propext, Classical.choice, Quot.sound]`.

## Lean leaves

    ConnesWeilRH/Dev/C1G8R3ShiftedHardyKernelReduction.lean
    ConnesWeilRH/Dev/C1G8R3ShiftedHardyKernelReductionAudit.lean
