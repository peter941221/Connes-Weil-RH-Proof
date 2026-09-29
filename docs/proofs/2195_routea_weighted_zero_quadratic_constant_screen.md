# Route A record 2195: quadratic Laplace constant screen

## Decision

The live consumer remains the healthy `CompactLog` B5 same-owner signed
`qw >= 0` margin. The candidate owner is the record-2109/2187 owner
(`gamma = 39.25244858548658`, `delta = 0.445`, `scale = 0.8`). The decision
question was whether the generic global quadratic-decay constant is already
too large to fit the candidate signed margin.

## Candidate screen

On a five-real-part strip grid and 2000-height sampling points, the sampled
lower screen for

```text
sup |t/(2*pi)|^2 * |laplaceAt F (sigma + i*t)|
```

was `C_lower = 2315.341509844046`, hence
`B_lower = (2*pi)^2 C_lower = 91406.0190223267`. Repricing the existing
analytic multiplicity formula with the diagnostic `xi(2) = pi/6` scale gives
`spectralMultiplicityConstant ≈ 301.83032993648527`; the resulting lower
screen for the high-shell budget is `1.103564355e8`, or
`6.58688e-5` of the candidate signed-margin anchor
`1.675397327895099e12`.

## Verdict

`GENERIC-C-PATH-NO-GO` did not fire on this candidate: the sampled lower
screen leaves substantial headroom. This is only a routing signal. It is not
an upper bound, interval enclosure, complete-owner result, or producer/RH
claim. The next live task is to outward-enclose the derivative/Laplace
constant and the shell-zero prefix for the actual owner.

## Verification

The heavy numeric screen completed through the resource wrapper with exit 0:
`results/20260929_weighted_zero_quadratic_constant_screen_2195.log`.
The transparent reprice also completed with exit 0:
`results/20260929_weighted_zero_quadratic_constant_reprice_2195.log`.
