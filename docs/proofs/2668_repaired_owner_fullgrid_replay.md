# Record 2668 - repaired-owner full-grid replay

**Verdict: REPAIRED-OWNER-REPLAY-PASS; C3' mathematical gate remains open.**

This replay injects the 2338 exact-interpolation coefficient-ball midpoints,
casts them to binary64, and checks their MD5 values against the 2665 treatment
arm before running the unchanged 2359 evaluator. It therefore closes the
owner-selection mistake identified in the 2667 erratum at the numerical replay
level.

## Readback

```text
+-----------------------------------------------+------------------+
| quantity                                      | value            |
+-----------------------------------------------+------------------+
| nodes                                         | 776611           |
| workers / span                                | 16 / 20001       |
| spans                                         | 39               |
| repaired base MD5                             | 31be9068...      |
| repaired correction MD5                       | d769f6a5...      |
| binary64-roundup base_M0                     | 2.686714329658   |
| binary64-roundup base_D2                     | 8606.214397684   |
| binary64-roundup corr_M0                     | 90.787882249     |
| binary64-roundup corr_D2                     | 125446.711378528 |
| four-channel roundup sum                     | 134146.400372791 |
| roundup sum / knownError2109                 | 0.0017981722     |
+-----------------------------------------------+------------------+
```

The same-expression audit is `directed_span_dominates_exact_binary64_sum`; all
four channels pass. The artifact separately retains the raw MPFR-term span
comparison, whose fourth channel is false. That path does not replay the
audited binary64 term expression, so it is diagnostic and is not used as the
same-expression witness. The final directed integral comparison also passes
for all four channels. These evaluator controls do not prove that the sampled
expression encloses the mathematical integrand or its tail.

The MD5 values differ from the 2275 captured owner and equal the 2665 repaired
treatment values. The lower replay sum is therefore a real owner-specific
measurement, not a relabeling of the 2667 captured-owner result.

## Nonclaims

The replay still does not prove pointwise mathematical-term dominance, the
trapezoid remainder, Lean numeric import, actual-owner identity in the live
consumer, or the signed infinite-xi tail. It does not establish `chargeRest`,
producer GO, `SourceRH`, or RH.

## Evidence

- `scripts/routea_repaired_owner_fullgrid_2668.py`
- `results/2668_repaired_owner_fullgrid.json`
- `results/2338_exact_interpolation_repair.json`
- `results/2665_l1_margin_repair.json`
- `results/2422_repaired_shared_geometry_776611.json` (captured-owner control)
