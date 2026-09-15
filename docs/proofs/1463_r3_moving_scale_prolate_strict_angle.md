# 1463 — R3 moving-scale relative prolate strict angle

**Date:** 2026-09-15.

**Consumer:** the same healthy `CompactLog` B5 detector and finite visible-prime
owner whose remaining positivity route is `G8SameOwnerReadbackData`; no
universal B1/all-tests sign claim is involved.

## Formal result

The moving-scale compact Hardy compression has norm strictly below one.  The
extremal-vector argument rules out both signs: a fixed or negative-fixed
vector would have compact physical and scaled Fourier support, forcing its
Fourier transform to vanish on an exterior ray and hence all shifted moments
to vanish.  The moment-character density argument then forces the vector to
be zero.

For the relative prolate factor, let `M` be the complement of the positive
half-line projection, `B` the support-complement projection, `U_b` the
doubled-shift Hardy involution, and `C_b = M U_b M`.  The leakage
`L_b = M U_b B` has zero kernel on `range B`.  Since `||C_b|| < 1`,
`A_b = I - C_b^2` is invertible.  The identity
`L_b L_b^* = M - C_b^2` reconstructs every `x` in `range B` as
`L_b^* A_b^-1 L_b x`.  Thus a finite constant `K_b > 0` gives
`K_b^-1 ||x|| <= ||L_b x||` on that range.  Orthogonal decomposition between
the positive-half-line output and its complement yields an angle bound
`||F_b|| <= sqrt(1 - K_b^-2) < 1` for the standard prolate factor.  Exact
unitary conjugacy transfers the strict norm bound to the actual moving-scale
relative factor.

The already established actual interior-compression column square-sum now
combines with this strict angle and the exact defect identity to prove
square-summability of the relative Hilbert--Schmidt factor along every named
Hilbert basis.  `BasisHilbertSchmidtData` then gives `IsTraceClassAlong` for
its positive composition on that same basis.

Lean anchors:

- `doubledShiftEvenAdditiveInteriorCompression_norm_lt_one`
- `doubledShiftHardyStandardProlateFactor_norm_lt_one`
- `doubledShiftProlateHilbertSchmidtFactor_norm_lt_one`
- `doubledShiftProlateHilbertSchmidtFactor_summable`
- `doubledShiftProlatePositiveComposition_isTraceClassAlong`

## Limit of the result

This is not `G8SameOwnerReadbackData`: it supplies neither the cutoff
remainder's convergence to zero nor the trace readback limit to
`C1SameOwnerWeil.qw`.  The G8 cutoff/source reconnection, R3 detector sign,
same-detector semi-local positivity, C3, and RH remain open.

## Acceptance

The paired leaf and audit completed successfully in
`20260915_scale_prolate_strict_angle_audit_try2.log`:
3286 jobs, zero error lines, zero `sorryAx`, and seven `Quot.sound]`
terminators for seven axiom-print audits.  Every new declaration has exactly
`[propext, Classical.choice, Quot.sound]`.

Lean leaves:

    ConnesWeilRH/Dev/C1G8R3ScaleStrictAngle.lean
    ConnesWeilRH/Dev/C1G8R3ScaleStrictAngleAudit.lean
    ConnesWeilRH/Dev/C1G8R3ScaleProlateStrictAngle.lean
    ConnesWeilRH/Dev/C1G8R3ScaleProlateStrictAngleAudit.lean
