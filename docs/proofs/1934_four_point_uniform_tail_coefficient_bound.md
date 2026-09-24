# Record 1934: bounded-coefficient uniform tail

Date: 2026-09-24.

## Formal result

`C1FourPointHighShellTail.lean` now proves
`exists_uniform_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail`.

For fixed `rho`, `L >= 0`, and `epsilon > 0`, it supplies decay constants
`C4`, `C2`, `T` and an index threshold `N` such that, for every `n >= N` and
every span coefficient satisfying `|lambda| <= L`, the corresponding actual
four-point span square satisfies `FourthOrderSpectralTail` with `epsilon`.

The proof bounds the polynomial factor at `|lambda| = L` and then applies the
geometric decay of `(1/2)^n`. The result is owner-preserving and applies to
the actual selected owner at each later convolution index.

## Impact on the live obligation

The gate branch no longer needs to coordinate a separately chosen `lambda`
with the tail index. It only needs an explicit coefficient bound. The strict
determinant margin and a bound uniform enough in `rho` for the final producer
remain open.

## Verification

Focused build `20260924_fourpoint_tail_uniform5.log` completed successfully
(3810 jobs). The paired audit reports only `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` occurs.

Classification: FORMAL strict reduction; RH is not claimed.
