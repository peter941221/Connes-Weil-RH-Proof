# 1185 — Bombieri residual pinned to the same-owner spectral tail

## Status

**FORMAL interface; producer obligations remain open.**

## Landed brick

`C1HealthyYoshidaSpectralNegativity` now proves
`spectralHeightShellTail_abs_re_le_normTail`: the absolute real part of the
high-shell spectral tail is bounded by the corresponding sum of norms.

`C1BombieriP2Bridge` adds `BombieriQuadraticSpectralTailP2BridgeData`. Its
residual is exactly the high-shell tail of the same owner
`g.convolutionSquare`, rather than an arbitrary real. The constructor
`BombieriQuadraticSpectralTailP2BridgeData.toResidual` consumes the two-sided
tail estimate and the existing finite-form positivity theorem to obtain
`qw g ≥ 0`.

The contract is wired through the P2 aggregate and the pinned healthy-B5
`SourceRH` exit in `C1P2BilateralProfileExit`.

## What is still missing

The producer must prove, for the pinned orbit detector, (i) the exact
same-owner decomposition of `qw g` into the finite Bombieri form minus this
high-shell tail and (ii) domination of the norm tail by the finite quadratic
main term. Neither equality nor domination is assumed or numerically
manufactured here. Consequently P2 is not closed by this record.

## Acceptance

Focused batch `p2-spectral-tail-r2.log` completed successfully (3780 jobs),
with no `error:` lines and no `sorryAx`; audit declarations have only the
standard `[propext, Classical.choice, Quot.sound]` axioms.
