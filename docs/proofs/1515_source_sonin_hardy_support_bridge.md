# 1515 - Source-Sonin Hardy support bridge

## Status

Formal conditional support reduction; the physical B4 support premise remains
open.

## Result

For the genuine source Sonin projection `P`, Lean proves the exact support
identity

`E H P = H P`,

where `E` is the original radial support projection and `H` is the actual
Hardy--Titchmarsh involution. Consequently, if a source column `M` satisfies
`P M J = M J`, then every nonnegative widened shift has the automatic support
certificate

`E_wide H M J = H M J`.

The declarations are `sourceSoninProjection_hardy_radialSupport` and
`wideRadial_absorption_of_sourceSoninRangeHardy` in
`ConnesWeilRH/Dev/C1G8R3CompositeBoundaryEnergy.lean`. They use only the exact
intersection-projection absorption, the Hardy/Fourier conjugation identity,
and the existing wider-radial monotonicity lemma.

This narrows B4 for a future boundary factorization: its source-range part is
free, and only the complementary part needs a Hardy support argument. The
actual ambient-loss and Schur boundary columns have not yet been shown to be
source-range, so WO-B and the S3 energy target remain open.

## Acceptance

Focused build log: `/home/peter/rh/build-logs/1645_source_sonin_hardy_support.log`.
Audit build log: `/home/peter/rh/build-logs/1646_source_sonin_hardy_support_audit.log`.
Both completed successfully with no `error:` or `sorryAx`; the audit prints
only `[propext, Classical.choice, Quot.sound]` for the new declarations.
