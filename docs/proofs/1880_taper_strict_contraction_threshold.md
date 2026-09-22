# 1880 - Taper strict-contraction threshold

Date: 2026-09-23.

Status: Formally verified in Lean; the gap-weighted taper budget now has a
direct strict-contraction consumer.

`strict_taper_correction_of_gap_budget` proves that the explicit scalar
condition

```text
2 * card(ι) * ||target|| * windowTaperBound < alpha
```

implies

```text
2 * seminorm(0,0,taperCorrection) < 1.
```

The theorem consumes the same-owner gap and solve hypotheses and does not
replace the threshold with an assumed coefficient bound.  It is therefore the
precise analytic certificate still needed by the geometric contraction route.

Verification: WSL focused build `taper-threshold-20260923a.log`; successful
footer for 3551 jobs, zero `error:` lines, zero `sorryAx`, and the paired Audit
declaration uses only `[propext, Classical.choice, Quot.sound]`.

The scalar threshold itself is not yet proved for the selected detector or
target family.  Detector-specific semi-local positivity and RH remain open.
