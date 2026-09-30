# 2282: high-precision Chebyshev-basis Filon screen

Date: 2026-09-30

Decision: the current panel/degree Filon approximation is untrusted even after moving the arithmetic into an 80-digit Chebyshev-basis computation.

## Question

Does changing from a power-basis binary64 implementation to a high-precision Chebyshev-basis inner product remove the 2280 instability?

## Method

The same corrected width-a^2 owner and stored coefficients are used. For each panel, the amplitude is represented in the Chebyshev basis. The oscillatory moments are computed at 80 decimal digits, and the transform is evaluated at xi = 40, 80, 120, 160, 200. The profiles are 12 panels/degree 12, 18 panels/degree 16, and 24 panels/degree 20.

## Result

The pointwise profile refinement gate fails:

```text
profile transition       max base change       max corr change
12:12 -> 18:16                 2.6358x              7.3760x
18:16 -> 24:20                 1.0339x            187.5186x
```

The correction channel changes by about 187.5 times between the last two profiles at one of the audited xi points. This is not a directed enclosure and cannot supply hgap.

## Interpretation

The 2280 power-basis floating implementation was arithmetically unstable, as shown by 2281. The 2282 result shows that simply moving to high precision and a Chebyshev basis does not fix the current panel/degree approximation. The failure is now a combined approximation/residual-control failure, not merely binary64 roundoff.

Reopening this exact profile requires a named residual theorem, such as a uniform derivative bound for the panel interpolation error or an analytically integrated local representation that preserves the owner’s endpoint flatness. Do not keep increasing panels and degrees without such a bound.

## Nonclaims

- Selected xi points are not an infinite-tail certificate.
- High precision is not a directed interval enclosure.
- No hgap supplier, producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_chebyshev_basis_filon_screen_2282.py
python -m unittest discover -s scripts -p 'routea_chebyshev_basis_filon_selftest_2282.py' -v
```

## Erratum 2285

The original 2282 artifact used the same Chebyshev endpoint-coefficient bug as 2281. Its old numeric readings are superseded. After correcting `c_0` and `c_n`, the profile remains untrusted, with pointwise max changes `17.5547x` and `39.4779x` for 12:12 -> 18:16, then `1.8828x` and `484.0690x` for 18:16 -> 24:20. Thus the route-level approximation/residual concern remains, but the earlier arithmetic diagnosis was wrong.
