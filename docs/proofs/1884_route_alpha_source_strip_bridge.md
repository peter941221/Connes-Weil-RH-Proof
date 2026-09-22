# 1884 - Route-alpha source-zero strip bridge

Date: 2026-09-23.

Status: Formally verified in Lean; connects the real-part taper envelope to
the actual source-zero owner.

The theorem `routeAlphaRealPartBound_le_four_exp_of_sourceNontrivialZero`
consumes the existing source-zero facts
`0 < Re(rho)` and `Re(rho) < 1` and derives

```text
windowTaperRealPartBound a b (routeAlphaNodes rho)
  <= 4 * exp(max(|a|, |b|)).
```

This removes a caller-side assumption from the route-alpha threshold input.
It does not prove the Gram-gap lower bound `alpha`, the strict scalar
threshold, detector-specific semi-local positivity, or RH.

Verification: WSL focused build `route-alpha-strip-1884a.log`; successful
footer for 3686 jobs, zero `error:` lines, zero `sorryAx`, and the paired
Audit declaration uses only `[propext, Classical.choice, Quot.sound]`.
