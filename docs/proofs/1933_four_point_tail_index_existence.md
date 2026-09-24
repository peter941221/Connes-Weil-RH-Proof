# Record 1933: existential closure of the four-point high-shell index

Date: 2026-09-24.

## Formal result

`C1FourPointHighShellTail.lean` now proves
`exists_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail`.

For every fixed base/correction owner, zero parameter `rho`, span coefficient
`lambda`, and positive tail budget `epsilon`, there exist nonnegative decay
constants `C4`, `C2`, a contraction threshold `T`, and a convolution index `n`
such that the selected four-point span square satisfies
`FourthOrderSpectralTail` with that `epsilon`.

The proof chooses the existing uniform quartic/quadratic decay constants and
uses `(1/2)^n -> 0`; the full scalar tail budget therefore tends to zero for
fixed `rho` and `lambda`. This removes the former conditional `hsmall` premise
from the producer-facing existential tail statement.

## Scope

This is a genuine Cut-1 reduction, not the determinant sign. It does not make
`epsilon` uniform in `rho` or `lambda`, and it does not choose the gate vertex.
The remaining joint obligation is now: obtain a parameterized positive gate
margin and coordinate its resulting `lambda` with a positive epsilon before
choosing `n`.

## Verification

Focused build `20260924_fourpoint_tail_exists2.log` completed successfully
(3810 jobs). The paired audit reports only `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` occurs.

Classification: FORMAL strict reduction; RH is not claimed.

## Uniform coefficient-bound strengthening

The same leaf now proves
`exists_uniform_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail`.
If `|lambda| <= L`, with `L >= 0`, then one threshold `N` works for every
`n >= N` and every such `lambda`, for fixed `rho` and positive `epsilon`.
The proof bounds the coefficient factor by the endpoint `L` before applying
geometric decay. This removes the possible circularity in which a gate-picked
`lambda` would otherwise have to be fixed before choosing the convolution
index.

Focused build `20260924_fourpoint_tail_uniform5.log` completed successfully
(3810 jobs); the audit remains standard-axiom-only with zero `sorryAx`.
