# 2289: phase-aware Filon amplitude remainder price

Date: 2026-09-30

Decision: candidate mechanism remains OPEN; the raw amplitude residual price is below the hgap budget for one profile, but no supplier exists yet.

## Method

Unlike classical GL, the oscillatory phase is integrated analytically. The sampled remainder price is applied only to the non-oscillatory corrected owner amplitude. For degree `d`, the screen uses the Lagrange residual shape with the sampled `(d+1)`-st amplitude derivative. The sampled derivative maxima are not uniform bounds.

## Result

```text
profile       base amplitude price       corr amplitude price
12:4          1.6294e7                   2.0263e7
12:6          7.5066e8                   3.1398e8
12:8          2.0096e10                  4.0038e9
24:4          1.8145e6                   1.5000e6
24:6          1.8675e7                   6.0794e6
24:8          1.1411e8                   1.7013e7
```

The `24:4` sampled amplitude residual price sums to about `3.3145e6`, below the raw `1e7` gap budget. This is the first phase-aware remainder profile that passes a preliminary price gate.

## Required next proof

The sampled derivative price is not a certificate. The next step is a directed, uniform fifth-derivative enclosure for the complete corrected owner amplitude on each of the 24 panels. The enclosure must preserve the family sum before modulus or explicitly book the cancellation loss. After that, the transform residual must be propagated through the actual kernel-weighted quadratic functional; the raw amplitude price cannot be called an `hgap` charge by itself.

## Nonclaims

- Sampled amplitude derivatives are not uniform bounds.
- This is not a quadrature certificate or an hgap supplier.
- The finite window and infinite xi tail remain separate.
- No producer GO, selected-detector readback, or RH conclusion follows.

## Reproduction

```text
python scripts/routea_filon_amplitude_remainder_price_2289.py
python -m unittest discover -s scripts -p 'routea_filon_amplitude_remainder_selftest_2289.py' -v
```
