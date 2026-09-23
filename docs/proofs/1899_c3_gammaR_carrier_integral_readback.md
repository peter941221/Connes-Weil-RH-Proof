# Record 1899 — C3' carrier-square Gamma_R integral readback

Date: 2026-09-23.

## Consumer and scope

This brick serves the healthy-`CompactLog` B5 route's detector-specific C3'
Archimedean determinant face. It connects the established carrier frequency
shift and pointwise Gamma_R shifted-weight identity to the complete
same-owner archimedean term of the actual carrier-modulated convolution
square. The selected detector's semilocal nonnegativity remains the consumer;
this record is not itself a producer of that sign.

## Formal result

`ConnesWeilRH/Dev/C1C3SigmaShiftReadback.lean` proves:

- `gammaRIntegrand_carrierModulate_eq_carrierShifted`: the two centered
  Laplace weights shifted by `-γ*i` give exactly the Gamma_R integrand of the
  modulated test;
- `integrable_carrierShiftedGammaRIntegrand`: full-line integrability follows
  from the existing center-two same-owner integrability theorem;
- `normalized_gammaR_carrierModulate_re_eq_archimedeanTerm`: the normalized
  integral reads back to the complete archimedean term;
- `convolutionSquare_carrier_eq`: the modulated test's convolution square is
  the modulation of the original square;
- `archimedeanTerm_carrierSquare_eq_shiftedGammaR`: the resulting exact
  integral readback for the actual carrier square.

The proof composes the formal identities in
`C1C3CarrierFourierShift.lean` with
`C1XiCenterTwoGamma.normalized_gammaR_centerTwo_re_eq_archimedeanTerm` and
`integrable_gammaRIntegrand_centerTwo`. It introduces no new analytic
assumption.

## Boundary

This is an integral-level carrier/Gamma_R readback, not the paper's
Fourier-multiplier identity expressing the archimedean term as a weighted
Fourier integral against `c3Sigma`. It proves no sigma sign, no
envelope-dependent remainder bound, no selected-detector diagonal sign, and
no finite visible-prime budget. The exact same-owner determinant estimate and
C3' semilocal positivity remain open; there is no RH conclusion.

## Verification

Focused build log: `build-logs/20260923_c3_sigma_readback3.log` (WSL mirror).
Both the owning module and paired Audit completed successfully (3791 jobs),
with no `error:` or `sorryAx` lines. All six declarations printed by the
paired Audit have exactly `[propext, Classical.choice, Quot.sound]`.
