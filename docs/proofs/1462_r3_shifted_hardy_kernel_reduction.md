# 1462 — R3 shifted Hardy kernel reduction

**Date:** 2026-09-15

**Consumer:** healthy CompactLog, B5-shaped detector-specific
`0 <= C1SameOwnerWeil.qw g`.

## Result

The shifted crossing is now connected to a single compact-window analytic
object.  With `P` the positive-half-line projection, `M = 1 - P`, and
`K_b = T_(2b) * H`, define

    Interior_b = M * K_b * M.

The formal declarations prove:

1. `shiftedRaw_b = -Interior_b * K_b * P`;
2. the inverse translation conjugacy from the shifted crossing back to the
   original raw crossing;
3. square-summability transfer through the bounded translation factors;
4. the exact adjoint defect identity for the relative prolate factor;
5. the conditional implication

       strict_angle(A_b) + square_sum(Interior_b)
         -> square_sum(A_b).

6. the expected scaled additive Fourier kernel on `[-1,1]` is continuous,
   and its compact-interval operator has a formally proved basis square-sum.
7. at zero shift, the actual interior compression is exactly the existing
   unit-scale interior Fourier compression;
8. the zero-shift interior compression therefore has the existing unit-scale
   basis square-sum certificate.
9. for general `b`, the actual interior compression transported to the
   additive-even carrier is exactly the literal interval projection, followed
   by the induced additive dilation, followed by additive Fourier, followed by
   the same literal projection.
10. the scale-dependent Schwartz transport is explicit: it is multiplication
    by `exp b` followed by argument dilation by `exp (2*b)`.
11. on the Schwartz core, the scaled Fourier coefficient is exactly the
    explicit model-kernel coefficient, and the model compact interval operator
    is the restricted scaled Fourier transform of the core product.
12. the actual additive dilation sends every bundled even-Schwartz input to
    the bundled Schwartz function with the exact `exp b` half-density factor
    and `exp (2*b)` argument dilation.
13. on the bundled bump-Schwartz core, the transported literal interval
    projection/Fourier/projection operator equals the explicit finite-window
    model factor.
14. the core equality extends to the full healthy even additive carrier by
    interval `DenseRange` and the idempotent literal projection; the proof
    uses the projection image rather than claiming the compact core is dense
    in the unprojected global `L2`.
15. the compact-kernel square-sum transfers through the full-carrier equality
    to the actual additive and shifted-Hardy interior compressions, using the
    exact unitary carrier change.
16. the actual shifted relative prolate factor is unitarily conjugate to the
    standard `prolateFactor` for `doubledShiftHardyTranslationEquiv b`, and its
    operator norm is exactly the norm of that standard factor.

The proof uses existing projection laws, the previously accepted translation
bridge, the generic strict-contraction defect lemma, and norm invariance under
linear isometric equivalences.  No numerical premise or new axiom is
introduced.

## Mathematical interpretation

The large half-line crossing is no longer the primary analytic target.  After
the translation, only the two finite Hardy windows remain in the middle.  On
the even additive carrier, this has now been written as the expected
continuous kernel with a scale-dependent phase, and the generic compact-kernel
theorem proves its Hilbert--Schmidt square-sum.  The operator identification
between that model kernel and `Interior_b` is now formal on the full healthy
even additive carrier.  The exact zero-scale identity anchors the constants
and carrier normalization, but does not by itself identify the nonzero-scale
dilation.
The general carrier transport and its bundled even-Schwartz readback are now
formal.  The compact Fourier-dilation kernel identity for the actual literal
operator is now formal on the full healthy even additive carrier.  The
functional-analytic extension uses interval core density and the literal
projection image.  The model-side coefficient and interval readback are
formal on the core.

The exact shifted-factor conjugacy further removes the shifted carrier
coordinates from the strict-angle problem, but supplies no strict contraction
estimate.

The remaining independent target is the strict relative angle.  The current
leaf reduces its norm to the standard prolate factor at the translated Hardy
parameter, but does not prove that the norm is strictly below one.  A separate
analytic proof is still required; a direct positive trace estimate remains a
possible alternative route, not a proved substitute.

## Boundary

This is not yet the detector-specific `qw >= 0` theorem.  The compact-kernel
square-sum and its transfer to the actual interior compression are formal; the
strict angle, positive trace/readback, R3 sign, and RH remain open.

## Acceptance

    /home/peter/rh/build-logs/1477_conjugation_main_audit_try1.log

`Build completed successfully (3284 jobs)`, zero error lines, zero `sorryAx`,
and fifty-four audit `Quot.sound]` terminators.  The new conjugacy and norm
equality declarations use only `[propext, Classical.choice, Quot.sound]`.

    /home/peter/rh/build-logs/1475_hs_transfer_audit_try1.log

The 1475 transfer build completed successfully (3284 jobs), with zero error
lines, zero `sorryAx`, and forty audit `Quot.sound]` terminators.  Its audited
declarations use only `[propext, Classical.choice, Quot.sound]`.  The preceding additive
transport acceptance is `1464_additive_transport_audit_try7.log`; the prior
zero-scale anchor acceptance is `1463_zero_anchor_try4.log`, and the prior full
reduction acceptance remains `1462_shifted_hardy_formal_audit_try7.log`.
