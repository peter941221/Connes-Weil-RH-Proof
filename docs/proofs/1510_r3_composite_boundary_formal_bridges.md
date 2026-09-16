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
