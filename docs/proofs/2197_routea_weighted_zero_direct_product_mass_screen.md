# Route A record 2197: direct-product mass screen

## Consumer and owner

The live consumer remains the healthy `CompactLog` B5 same-owner signed
`qw >= 0` margin. The candidate owner is unchanged from records 2187 and
2196 (`gamma = 39.25244858548658`, `delta = 0.445`, `scale = 0.8`).

## Sharper mechanism

Record 2196 took absolute values before forming the family sums. This screen
instead forms the complete base and correction functions on the physical
support, including their analytic second derivatives, and then prices

```text
min(||base''||_1 ||correction||_1,
    ||correction''||_1 ||base||_1) / (2*pi)^2.
```

This retains signed cancellation among the family terms while remaining an
owner-local direct-product bound.

## Result

Using 240001 physical-support nodes, 101 strip real parts, and the same
candidate coefficient solve, the measured screen gives

```text
C_upper                 = 77444.14398633591
B_upper                 = 3057372.2573045553
high-shell budget upper = 3691230708.643563
candidate margin        = 1675397327895.099
budget / margin         = 0.0022031972041408675
```

The direct-product mechanism therefore restores substantial candidate
headroom; it is not frozen by the 2196 failure.

## Status

This is still a measured screen, not an interval certificate: coefficient
solve error, grid/trapezoid error, and complete-owner transfer remain unpaid.
The next required brick is an outward enclosure of the direct base/correction
functions, their second derivatives, and the coefficient solve. If that
enclosure consumes the roughly `1/0.0022 ≈ 454` margin factor, this branch
fails; otherwise it supplies the live `B_zm < epsilon` candidate.

## Verification

The heavy probe completed through the resource wrapper with exit 0:
`results/20260929_weighted_zero_direct_product_mass_screen_2197.log`.
