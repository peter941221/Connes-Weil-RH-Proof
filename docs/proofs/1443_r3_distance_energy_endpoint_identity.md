# 1443 — R3 distance-energy endpoint identity

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 endpoint bridge.

## Result

For every input `v` and every stage `n`, the actual intersection projection
`r_b` satisfies the exact identity

```text
||T_b^n v - r_b v||^2
  = ||T_b^n v||^2 - ||r_b v||^2.
```

The proof combines the fixed projection identity `r_b T_b^n = r_b` with the
orthogonal-complement Pythagorean decomposition for `r_b`. It is a same-owner
identity on the actual carrier, not a spectral-gap estimate.

## Consequence and boundary

The no-gap strong-limit problem is now equivalent to the scalar endpoint
exhaustion condition

```text
ciInf_n ||T_b^n v|| = ||r_b v||.
```

Records 1442 and 1441 then consume this equality into strong convergence and
identify the limit. Proving this scalar exhaustion equality itself, followed
by the detector-weighted trace estimate, remains open; no R3 sign or RH claim
is made here.

## Acceptance

The paired audit build log
[`023_distance_sq_try3.log`](/home/peter/rh/build-logs/023_distance_sq_try3.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and thirty-eight standard `Quot.sound` entries.
