# 1510 — R3 composite boundary formal bridges

Date: 2026-09-16.

Status: FORMAL, conditional reduction only. No composite support estimate and
no RH conclusion is claimed.

Consumer: WO-B in map 042, on the healthy-`CompactLog` B5 same-owner G8
readback route.

## Landed declarations

`C1G8R3CompositeBoundaryEnergy.lean` now contains the exact wider-half-line
difference, arbitrary-window strip Hilbert--Schmidt columns, the composite
radial OUT reduction, the Hardy conjugation bridges, and the composite
internal-gap OUT reduction. The latter two bridges are separate declarations
so the deep operator reassociation is independently kernel-checked.

The owning and audit builds completed successfully with 3958 jobs, zero
`error:` lines, zero `sorryAx`, and standard axioms
`[propext, Classical.choice, Quot.sound]`.

## Boundary

The open inputs remain exactly the composite support facts `hwide` and
`hwideHT`. The ambient factor `M` remains between the root convolution and
the source inclusion throughout; no invalid bounded-right-precomposition
shortcut is used. Thus this record closes the formal B3/B4 reduction layer,
not the analytic square-summability obligations themselves.

## 2026-09-16 wider-radial support absorption (record 1530)

`C1G8R3CompositeBoundaryEnergy.lean` now proves
`wideRadial_absorption_of_radialSupport`: if an ambient factor `M` is fixed by
the original radial projection, then monotonicity of the radial projector
family makes it fixed by `wideRadialScale lambda s` for every `s >= 0`.
This removes the `hwide` premise for that subclass. It does not establish the
premise for the actual visible-prime factors `M_p`, nor for their
Hardy-Titchmarsh conjugates; B3/B4 remain open there.

The same monotonicity argument is now exposed for the Hardy-Titchmarsh
channel: `wideRadial_absorption_of_hardyRadialSupport` reduces `hwideHT` to
the original-scale radial support of `H ∘L M`. The actual conjugated boundary
factors still require that original-scale support input.

The support consumer now matches the B3/B4 interfaces exactly. The source
variants `wideRadial_absorption_of_sourceRadialSupport` and
`wideRadial_absorption_of_sourceHardyRadialSupport` require only the original
scale identities for `M ∘L sourceInclusion` and
`H ∘L M ∘L sourceInclusion`, respectively. No global range hypothesis is
needed. The visible-prime factors still need these original-scale identities.

## 2026-09-16 concrete forward transport instance (record 1535)

The owning file now proves `normalizedPrimeEulerFrameTransport_sourceRadialSupport`
and its wider-scale corollary
`normalizedPrimeEulerFrameTransport_sourceWideRadialSupport`. The proof uses
the committed causal theorem for `ccm24PrimeEulerTransportEquiv` together with
radial membership of `sourceInclusion`; scalar normalization preserves the
closed radial subspace, and record 1530 supplies the wider-scale step.

This discharges `hwide` for the genuine forward one-prime transport when it is
the factor immediately before the source inclusion. It does not discharge the
actual boundary factor, which contains adjoint transport and projection
blocks; those can leave the radial half-line and still require a separate
support or leakage estimate.

The same bridge is now proved for the complete finite forward transport
`finiteEulerTransportOperator family`, including its wider-scale corollary.
Thus any boundary factorization that exposes the full forward Euler product at
the source edge can use the consumer without an additional support premise.

## 2026-09-16 adjoint radial leakage bridge (record 1540)

The owning file now proves the exact operator identity
`normalizedPrimeEulerFrameTransport_adjoint_radialLeakage`: after the radial
cutoff, the adjoint one-prime transport equals
`-(q * (1+q)^(-1))` times `primeEulerRadialBoundaryStep`, where `q` is the
visible-prime Euler coefficient. The proof expands the normalized adjoint,
uses idempotence of the radial projection, and identifies the remaining
positive-translation complement with the committed boundary step.

This removes the support mystery for the outer part of the actual adjoint
transport: it is exactly an existing radial boundary channel. The estimate,
the inner radial part, and the remaining metric/projection factors are still
open, so B3/B4 and the G8 readback remain conditional.

The corresponding ambient-loss form is also formal:
`primeEulerAmbientLossFactor_adjoint_radialLeakage` identifies the radial
complement of the adjoint loss factor with
`primeEulerAmbientLossScale p` times the same boundary step. This matches the
ambient-loss column used by the actual Schur boundary owner and isolates its
outer channel without introducing a new estimate.

## 2026-09-16 actual Schur-column leakage (record 1545)

The owning file now proves
`suffixEulerFrameAmbientLossColumn_radialLeakage`.  Since the old suffix
frame is radially supported, the radial complement of the actual ambient-loss
column is exactly
`primeEulerAmbientLossScale p • (primeEulerRadialBoundaryStep lambda p ∘L oldFrame)`.
This is the first bridge from the abstract adjoint leakage identity to the
actual physical Schur column.  It is an exact equality only; no Hilbert--Schmidt
or source-basis square-sum estimate follows from it.

The same file exports `suffixEulerFrameSchurStep_oldFrame_radialSupport`,
separating the actual frame support fact from the ambient-loss leakage
calculation.  This is a reusable formal premise for any later root-window
energy transfer through the actual old frame.

## 2026-09-16 wide-scale support for the actual loss column (record 1555)

A new exact support theorem proves
`suffixEulerFrameAmbientLossColumn_wideRadialSupport` at the canonical width
`s = log p`.  The proof transports the old-frame support from `lambda` to
`wideRadialScale lambda (log p)`, then uses the shifted support lemma for the
positive translation in the antiresonant loss factor.  Consequently the
`hwide` premise of the composite radial B3 reducer is no longer an external
assumption for this ambient-loss column at that width.  The resulting compact
window estimate and the coupled inner channel are still separate obligations.

## 2026-09-17 B3 radial energy for the actual ambient-loss column (record 1558)

The owning file now adds a source-column form of the composite radial reducer.
Any bounded column `A : sourceSoninCarrier lambda ->L Carrier` is represented as
`(A ∘L J†) ∘L J`, using the isometric source inclusion `J`; the existing B3
proof then transfers verbatim.  Combining this wrapper with
`suffixEulerFrameAmbientLossColumn_wideRadialSupport` at `s = log p` gives the
unconditional formal theorem
`suffixEulerFrameAmbientLossColumn_compositeRadialLeg_sourceBasis_normSq_summable`.
Thus the root-convolved radial OUT energy of the actual ambient-loss column is
now closed.  The theorem is a square-sum transfer only; the coupled inner
metric/projection channel and B4 remain open.

## 2026-09-17 B3 transfer through arbitrary source columns (record 1560)

The B3 reducer now has a source-column interface
`compositeRadialLeg_sourceColumn_normSq_summable`: for any bounded
`A : sourceSoninCarrier lambda ->L Carrier`, the proof realizes `A` as
`A ∘L J† ∘L J` and transfers the existing composite estimate.  A direct
postcomposition lemma then gives the same square-sum after any bounded
ambient readout.  Together with record 1555 this closes the radial OUT
energy of the actual ambient-loss physical channel, including bounded
ambient-row readouts.  No claim is made for the inner metric/projection or
Hardy-conjugated channel.

## 2026-09-17 Boundary-dagger wide support and radial OUT transfer (record 1561)

The actual rectangular Schur boundary dagger now has a formal wide-radial
support identity at `s = log p`:
`suffixEulerFrameSchurStep_boundaryDagger_wideRadialSupport`.  The proof uses
the positive translation in the adjoint normalized Euler transport, monotonicity
of the radial projection, and containment of the new Schur range in the
original radial half-line.  Instantiating the generic source-column B3 wrapper
gives source-basis square-summability for the root-convolved boundary dagger,
and a postcomposition form for bounded ambient rows.  Thus both physical
boundary coordinates have their radial OUT B3 estimate.  The Hardy-conjugated
B4 estimate and the survivor IN estimate remain open.

## 2026-09-17 Source-column interface for B4 (record 1562)

The B4 internal-gap reducer now also has a source-column interface
`compositeGapLeg_sourceColumn_normSq_summable`.  It represents an arbitrary
bounded source column `A` as `A ∘L J† ∘L J`, exactly as in B3, and reduces the
Hardy support premise to the source-composed identity
`E_(lambda exp(-s)) H A = H A`.  This is a formal interface reduction only;
no Hardy support theorem for the actual ambient-loss or boundary-dagger
columns has been claimed.

The two concrete source-column instances are now named as well:
`suffixEulerFrameAmbientLossColumn_compositeGapLeg_sourceBasis_normSq_summable`
and
`suffixEulerFrameSchurStep_boundaryDagger_compositeGapLeg_sourceBasis_normSq_summable`.
They remain conditional exactly on their respective source-composed Hardy
support identities.
