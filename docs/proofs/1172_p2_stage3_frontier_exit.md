# Record 1172 — P2 Stage-3 frontier exit (superseded)

Date: 2026-09-06

## Original result

The original draft attempted to package the two named Stage-3 facts for each
right-oriented off-line detector:

1. Hilbert–Schmidt summability of the convolution factor
   `F_g = stage3FamilyFactor g` on a fixed global basis;
2. the same-owner trace readback
   `Re Tr(F_g†F_g) = qw(g)`.

The existing `stage3Remainder_family_for_g` was intended to supply a
positive-pair limit family.

The draft interface itself built successfully in 3769 jobs, with no `error:`
lines or `sorryAx`; that build does not make its premises satisfiable.

## Correction

The route is not viable on the stated owner.  The existing formal theorem
`C1Stage3BareHSObstruction.bareHS_iff_zero_test` proves that whole-line
`stage3FamilyFactor` is Hilbert--Schmidt iff the compact-log test is zero.
Therefore no nontrivial healthy detector can satisfy the draft FRONTIER-HS
premise.  The draft `SourceRH` theorem was removed from the live P2 module.
Future Stage-3 work must use a windowed or renormalized factor; P2/RH remain
open.
