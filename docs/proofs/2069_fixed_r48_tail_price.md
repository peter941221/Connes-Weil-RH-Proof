# 2069 - Fixed-r48 owner-specific tail price

Date: 2026-09-28.

Status: FIXED-R48-TAIL-GO-CANDIDATE.

Using the actual one-copy G8-H owner, the m=6400 coefficient path, and a
single fixed integration-by-parts rung `r = 48`, the interval-variation upper
skeleton from record 2068 prices the tail as:

```text
N48 upper             = 1.2466403887652727e81
160..1e6 tail         = 7.068567822135646e-260
 tail / |Q1600|       = 2.0752978047944553e-272
 tail / L2 charge     = 1.6020449851959417e-270
```

This is stronger than the min-over-r candidate because it removes the need to
certify a rung-selection envelope: one fixed r=48 bound suffices numerically.

Decision: `FIXED-R48-TAIL-GO-CANDIDATE`.

Remaining proof obligations:

1. turn the 2068 interval skeleton into a valid total-variation upper bound;
2. prove the endpoint/root completeness statement for `P_48`;
3. replace the finite `1e6` cutoff with an explicit algebraic infinity bound;
4. attach the tail to the full same-owner signed C3' enclosure.

The result is not yet a producer theorem or an RH claim.

Artifact: `results/2069_fixed_r48_tail_price.json`.
Script: `scripts/routea_fixed_r48_tail_price_2069.py`.
