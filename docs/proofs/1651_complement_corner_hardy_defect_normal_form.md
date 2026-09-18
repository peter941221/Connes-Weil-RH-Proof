# 1651 - S3 complement corner in shifted-Hardy coordinates

Date: 2026-09-19.

Status: formal exact reduction; the Schatten estimate remains open. RH is not
claimed.

The existing leakage consumer requires square summability of

`R_b (I - Q_0) R_b`,

where `R_b` is the doubled-shift radial projection and `Q_0` is the unit
Fourier-support projection. The theorem
`doubledShiftComplementCorner_conjugate_eq_hardyDefect` now proves its exact
coordinate form:

`T_b R_b (I-Q_0) R_b T_b^{-1} = P - P K_b P K_b P`.

Here `P` is the positive-half-line projection and `K_b` is the shifted Hardy
involution. The proof uses only the already formal radial and Fourier
intertwining identities plus the inverse translation identities. The paired
Audit reports exactly `[propext, Classical.choice, Quot.sound]`.

This is a route-level clarification, not a closure: the previously available
square-summability theorem concerns the opposite Hardy block, the interior
compression `(I-P) K_b (I-P)`, and does not imply square summability of the
P-side corner above. The remaining S3 producer is therefore a genuine
P-side Hankel/Schatten estimate (or a different same-owner sign/readback
argument that avoids it).

Acceptance: build log `1651_complement_corner_final2.log`; 3285 jobs,
zero `error:` lines, zero `sorryAx`, and the standard three axioms.
