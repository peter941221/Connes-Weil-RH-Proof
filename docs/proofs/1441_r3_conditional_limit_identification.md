# 1441 — R3 conditional strong-limit identification

**Date:** 2026-09-14.

**Status:** FORMAL / GREEN.

**Consumer:** the healthy-`CompactLog`, B5-shaped same-owner conclusion
`0 <= C1SameOwnerWeil.qw g`, through the R3 endpoint bridge.

## Result

For the actual doubled-shift alternating product `T_b` and intersection
projection `r_b`, the audited leaf proves the following conditional theorem:

```text
if T_b^n v -> w strongly,
then w = r_b v.
```

The proof has three exact pieces:

1. the shifted sequence `T_b^(n+1) v` has the same limit as `T_b^n v`;
2. continuity of `T_b` therefore makes the limit a fixed vector, and the
   previously formal fixed-space theorem puts it in the doubled-shift Sonin
   intersection;
3. a finite induction proves `r_b T_b^n = r_b`, so continuity of `r_b` and
   uniqueness of limits identify the fixed limit with `r_b v`.

No strong-limit existence theorem, angle gap, trace-class estimate, detector
sign, `SourceRH`, or RH conclusion is used.

## Boundary

The theorem removes the ambiguity of the endpoint but does not establish that
the orbit converges. The remaining R3 endpoint is now an existence theorem for
the no-gap alternating-projection limit (or an equivalent weighted spectral
argument), followed by the detector-weighted trace estimate.

## Acceptance

The paired audit build log
[`021_conditional_limit_try3.log`](/home/peter/rh/build-logs/021_conditional_limit_try3.log)
reports `Build completed successfully (3178 jobs)`, zero `error:` lines,
zero `sorryAx`, and thirty-four standard `Quot.sound` entries.
