# 027 — R3 shifted Hardy kernel reduction

**Date:** 2026-09-15.

**Status:** moving-scale strict angle, relative-factor HS square-sum, and its
same-basis positive-composition trace class are formal; G8 readback and R3
positivity remain open. Supporting route record, not an RH claim.

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
therefore exactly the norm of that standard factor.  The strict angle is now
formal at every real detector scale.  The compact moving-scale Hardy
compression has norm below one: a hypothetical extremizer would force compact
physical/Fourier support, then exterior-ray Fourier vanishing and moment
uniqueness force it to be zero.  For the relative prolate factor, the leakage
map `L_b = M * U_b * B` has zero kernel on the support-complement range.
Invertibility of `I - C_b^2`, with `C_b = M * U_b * M`, reconstructs vectors
from their leakage and supplies a uniform positive leakage lower bound.
Pythagoras then gives a strict contraction angle.  The full proof and
seven-declaration axiom audit are in
[1463](../proofs/1463_r3_moving_scale_prolate_strict_angle.md).

Combining this angle with the existing interior-compression column square-sum
and exact defect identity proves square-summability of the actual relative
Hilbert--Schmidt factor along every named basis.  Its positive composition is
`IsTraceClassAlong` along that same basis.

## Remaining boundary

The compact-kernel square-sum and its transfer to the actual additive and
shifted-Hardy interior compressions, the relative-factor strict norm bound,
and the factor's same-basis HS/positive-composition trace-class conclusions
are formal.  This is not the G8 cutoff remainder/readback: its vanishing
remainder and trace limit to the same owner's `qw` remain open, as do the R3
detector sign, same-detector semi-local positivity, C3, and RH.

## Latest acceptance

    20260915_scale_prolate_strict_angle_audit_try2.log

The moving-scale strict-angle leaf plus paired audit completed successfully
with 3286 jobs, zero error lines, zero `sorryAx`, and seven `Quot.sound]`
terminators for seven axiom-print audits.  These audit prints use only
`[propext, Classical.choice, Quot.sound]`.  The declaration set includes the
strict norm bound for the actual relative factor, its all-basis HS square-sum,
and the same-basis positive-composition trace-class owner.  Full design and
boundary details are in
[1463](../proofs/1463_r3_moving_scale_prolate_strict_angle.md).

## Acceptance

    1477_conjugation_main_audit_try1.log

The updated module plus paired audit completed successfully with 3284 jobs,
zero error lines, zero `sorryAx`, and fifty-four `Quot.sound]` audit
terminators.  The new audited declarations include the shifted-factor
conjugacy and exact operator-norm equality.  Every audited declaration has
only `[propext, Classical.choice, Quot.sound]`.

    1475_hs_transfer_audit_try1.log

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
    ConnesWeilRH/Dev/C1G8R3ScaleStrictAngle.lean
    ConnesWeilRH/Dev/C1G8R3ScaleStrictAngleAudit.lean
    ConnesWeilRH/Dev/C1G8R3ScaleProlateStrictAngle.lean
    ConnesWeilRH/Dev/C1G8R3ScaleProlateStrictAngleAudit.lean
