# 1881 - Route-alpha healthy target norm bound

Date: 2026-09-23.

Status: Formally verified in Lean; target-side norm input for the taper
threshold.

The theorem `healthyDetectorNodeTarget_norm_le_one` in
`C1RouteAlphaOwner.lean` proves

```text
||healthyDetectorNodeTarget rho|| <= 1
```

for every rho.  The proof uses the actual four-node target definition: each
entry is either `0` or `-1`, with no assumption about the zero location beyond
the subtype membership.

Verification: WSL focused build `route-target-norm-20260923c.log`; successful
footer for 3686 jobs, zero `error:` lines, zero `sorryAx`, and the paired
Audit declaration uses only `[propext, Classical.choice, Quot.sound]`.

This closes only the target norm factor.  It supplies no lower bound for the
taper Gram gap, no `windowTaperBound` threshold, no detector-specific
semi-local positivity, and no RH conclusion.
