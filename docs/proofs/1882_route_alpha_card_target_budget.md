# 1882 - Route-alpha card-times-target budget

Date: 2026-09-23.

Status: Formally verified in Lean; the conservative finite-dimensional target
factor is reduced to an explicit constant.

The declarations `routeAlphaIndex_card_le_four` and
`routeAlpha_target_card_norm_le_four` prove

```text
card(routeAlphaIndex rho) <= 4
card(routeAlphaIndex rho) * ||healthyDetectorNodeTarget rho|| <= 4.
```

The first fact is the direct four-element Finset cardinality bound.  The
second combines it with record 1881's pointwise target norm bound.

Verification: WSL focused build `route-target-card-20260923c.log`; successful
footer for 3686 jobs, zero `error:` lines, zero `sorryAx`, and both paired
Audit declarations use only `[propext, Classical.choice, Quot.sound]`.

If this target family is connected to the taper threshold, the conservative
1880 condition specializes to `8 * windowTaperBound < alpha`.  No lower bound
for `alpha`, no taper-bound certificate, no detector-specific semi-local
positivity, and no RH conclusion follows here.
