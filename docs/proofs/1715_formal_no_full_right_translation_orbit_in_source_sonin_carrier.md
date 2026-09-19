# 1715 — Formal exclusion of a full right-translation orbit in the source carrier

Date: 2026-09-20

Status: formal Lean brick; this is a route obstruction, not an RH claim.

## Theorem

`sourceSonin_nonzero_not_closed_under_all_right_translations` proves at unit
scale that if `u` lies in the source Sonin carrier and every orbit element
`U_{-n}u` also lies in that carrier, then `u = 0`.

The proof uses only committed facts: the source Fourier-support projection
fixes every source-carrier element; its norm along the right-translated orbit
tends to zero; and logarithmic translation is an isometry.  Thus the
projected norm is simultaneously constant at `||u||` and convergent to zero.

## Route consequence

The proposed full-translation noncompactness argument cannot be used to kill
the S3 survivor-core estimate: its required carrier invariance is formally
false for every nonzero carrier vector.  This does not prove the estimate and
does not rule out a finite-tail, cutoff-dependent, or genuinely pointwise
kernel-diagonal argument.  The live S3 target remains the post-Tonelli
pointwise diagonal bound recorded in map 042.

Evidence: `ConnesWeilRH/Dev/C1G8R3TranslationOrbitCarrierNoGo.lean` and its
Audit leaf; focused build log `1715_translation_orbit_no_go_v3.log`, 3285
jobs, zero errors and zero `sorryAx`, with axioms exactly
`[propext, Classical.choice, Quot.sound]`.
