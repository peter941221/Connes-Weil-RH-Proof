# 2187 — Route-A weighted-zero-measure candidate screen

Date: 2026-09-29  
Status: `SCREEN-GO / CANDIDATE-OWNER-ONLY`; no producer closure.

## Decision contract

The screen targets the residual side of the same selected-detector consumer:

```text
finite prefix + omitted low-shell residual + high-shell tail
  -> spectral negativity -> same-owner qw(g) >= 0 -> SourceRH.
```

It does not replace the actual selected owner. The numerical owner is the
record-2109 style first-30 critical-line-zero construction at
`gamma = 39.25244858548658`, `delta = 0.445`, `scale = 0.8`.

## Probe

Using the 2185 weight

```text
W(F,z) = xiMultiplicity(z) * ||laplaceAt F (z - 1/2)||,
```

the probe evaluates the convolution-square modulus on the known critical-line
zeros below the `N = 7` shell cutoff `|Im z| < 256`, omitting zeros already
present as interpolation nodes. It uses `m = 6400` quadrature and the existing
owner construction.

```text
known shell zeros       111
omitted known zeros      90
sum W                    2.0626232011592017e-3
max W                    2.0331806378834196e-3
anchor multiplicity      1
budget / anchor          2.0626232011592017e-3
```

The candidate residual budget is therefore below the 2138 anchor by a factor
of about `485`. This is a useful price screen, not an interval certificate.

## Nonclaims and next gate

The source-zero owner is incomplete, all multiplicities were set to one, and
the stored matrix/quadrature path is not outward enclosed. The screen also
does not compare against the final signed `epsilon`; it only tests the
consumer-side residual budget. No producer theorem or RH claim follows.

The next decisive probe is an owner inflation audit: bound the omitted source
zeros and multiplicities, plus matrix/quadrature enclosure, and check whether
the total amplification remains below `~485`. If it exceeds that factor, the
weighted-zero residual mechanism is a scoped no-go for this owner class.

Evidence: `scripts/routea_weighted_zero_measure_screen_2187.py` and
`results/20260929_weighted_zero_measure_screen_2187.log` in the WSL mirror.
