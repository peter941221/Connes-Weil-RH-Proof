# Record 1900 — C3' high-tail sigma oscillation bound

Date: 2026-09-23.

## Consumer and target

This brick serves the healthy-CompactLog B5 route's carrier-square
Archimedean remainder. It gives a quantitative high-frequency modulus for
the same sigma function used in the C3' carrier shift; the intended next
consumer is integration against the Fourier profile of the selected detector
envelope. It is not a semilocal positivity producer by itself.

## Formal result

`ConnesWeilRH/Dev/C1C3SigmaOscillationBound.lean` proves
`abs_c3Sigma_sub_le_of_height_lower`:

```
1 <= R
R <= |xi| / 2
R <= |eta| / 2
--------------------------------
|c3Sigma xi - c3Sigma eta| <= 2 * |xi - eta| / R
```

The proof first subtracts the existing half-anchor reciprocal-series
identities, cancelling their common anchor and leaving the same-owner
reciprocal difference at each height. Each summand is bounded by
`(|xi - eta| / 2) / ((n + 1/4)^2 + R^2)`. A telescoping comparison bounds
the quadratic majorant's total by `4 / R`, giving the stated constant.
No floating-point certificate or new analytic assumption is used.

## Boundary

This is a high-tail modulus only. It does not establish the paper's
Fourier-multiplier identity, integrate the modulus against the selected
detector profile, control the complementary-frequency tail, or supply any
diagonal or visible-prime signs. The detector-specific signed budget and
C3' semilocal positivity remain open; no RH conclusion is claimed.

## Verification

Focused build log: `build-logs/20260923_c3_sigma_oscillation5.log` (WSL
mirror). The owning module and paired Audit completed successfully (3545
jobs), with no `error:` or `sorryAx` lines. All four audited declarations
have exactly `[propext, Classical.choice, Quot.sound]`.
