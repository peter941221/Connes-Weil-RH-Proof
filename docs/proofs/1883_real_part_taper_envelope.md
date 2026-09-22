# 1883 - Real-part taper envelope

Date: 2026-09-23.

Status: Formally verified in Lean; removes an avoidable imaginary-height loss
from the taper contraction interface.

The old `windowTaperBound` used

```text
sum_i exp(||nodes_i|| * max(|a|, |b|)).
```

For a real argument `x`, the exact modulus identity is
`||exp(conj(node) * x)|| = exp(Re(node) * x)`.  The new
`windowTaperRealPartBound` and
`windowTaperComb_norm_bound_of_realPart` therefore use

```text
sum_i exp(|Re(nodes_i)| * max(|a|, |b|)).
```

The gap-weighted seminorm and strict-contraction consumers were duplicated
with this sharper envelope as
`windowTaperCorrection_seminorm_zero_zero_le_of_gap_realPart` and
`strict_taper_correction_of_gap_budget_realPart`.

For the route-alpha nodes `{0, 1/2, 1, rho}`, assuming the standard strip
side conditions `0 <= Re(rho) <= 1`,
`routeAlphaRealPartBound_le_four_exp` proves

```text
windowTaperRealPartBound <= 4 * exp(max(|a|, |b|)).
```

This removes dependence on the imaginary height of `rho`, but it does not
prove a positive lower bound for the tapered Gram gap `alpha`, does not prove
the scalar threshold, and does not provide detector-specific semi-local
positivity or RH.

Verification: WSL focused builds
`taper-realpart-1883a.log` and `realpart-routealpha-1883d.log`; the latter
ended with `Build completed successfully (3686 jobs)`, zero `error:` lines,
zero `sorryAx`, and the paired Audit declarations use only
`[propext, Classical.choice, Quot.sound]`.
