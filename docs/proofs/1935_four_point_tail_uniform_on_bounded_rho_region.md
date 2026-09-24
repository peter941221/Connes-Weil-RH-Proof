# Record 1935: four-point tail uniform on bounded rho regions

Date: 2026-09-24.

## Formal result

`C1FourPointHighShellTail.lean` now proves
`exists_bounded_rho_uniform_nat_selectedOwner_fullOrbit_span_fourthOrderSpectralTail`.

Given `R >= 0`, `L >= 0`, and `epsilon > 0`, it supplies decay constants and
one threshold `N` such that for every complex `rho` with `||rho|| <= R`, every
`n >= N`, and every `lambda` with `|lambda| <= L`, the actual four-point span
square satisfies the same `FourthOrderSpectralTail` bound with `epsilon`.

The constants are chosen independently of `rho`; the polynomial height factor
is bounded by `R` and the span coefficient by `L`, after which geometric decay
in `n` supplies the common threshold.

## Impact

On each bounded rho region, Cut 1 is now fully uniform in the later
convolution index and gate coefficient. The remaining producer work is to
partition or control the hypothetical zeros so that the determinant branch
supplies suitable `R`, `L`, and a strict gate margin. No determinant sign or RH
claim is made here.

## Verification

Focused build `20260924_fourpoint_tail_rhobound8.log` completed successfully
(3810 jobs). The paired audit reports only `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` occurs.

Classification: FORMAL strict reduction; RH is not claimed.
