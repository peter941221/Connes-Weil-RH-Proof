# 1442 — R3 Fejér distance ledger to the intersection

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 endpoint bridge.

## Result

For every vector `z` in the doubled-shift Sonin intersection, the actual
alternating powers satisfy the Fejér-type estimate

```text
||T_b^(n+1) v - z|| <= ||T_b^n v - z||.
```

The distance sequence is therefore antitone and converges to its explicit
`ciInf` endpoint. The proof uses only contraction of `T_b` and the already
formal fact that `T_b z = z`; it does not insert an angle gap or a spectral
limit theorem. A paired consumer theorem proves that if the endpoint infimum
for `z = r_b v` is zero, then the orbit converges strongly to `r_b v`.

## Boundary

This is an orbit ledger, not a strong-convergence proof. The remaining
existence question is exactly whether the distance infimum to `r_b v` is zero
(or an equivalent no-gap alternating-projection exhaustion statement). The
conditional endpoint identification of record 1441 then supplies the unique
limit, and the detector-weighted trace estimate remains separate.

## Acceptance

The paired audit build log
[`022_fejer_distance_try3.log`](/home/peter/rh/build-logs/022_fejer_distance_try3.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and thirty-seven standard `Quot.sound` entries.
