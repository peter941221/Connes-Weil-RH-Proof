# 3239: weighted correlated midpoint enclosure

Status: Lean-verified object-alignment theorem; no sign claim.

Record 3236 enclosed the unweighted same-owner value at midpoint index 17168
with a correlated taxicab-norm ball. Record 3239 adds the exact real weight
required by the formal aggregate:

```text
weightedExternal3201 (-1/2) c theta x
= Re(exp((-1/2) * x) * externalPhysical2344 c theta x)
```

The proof uses an order-30 two-sided Taylor interval for the real exponential
at the exact rational midpoint. The weighted ball is then obtained by the
ball multiplication theorem, preserving one shared enclosure rather than
splitting the real and imaginary cancellation into independent family bounds.

The formal results are:

```text
record2680_middle_point_weight_ball_mem3239
record2680_middle_point_weighted_aggregate_ball_mem3239
record2680_middle_point_weighted_value_upper3239
```

Verification was performed in a Linux-native WSL2 ext4 workspace with:

```text
lean-toolchain = leanprover/lean4:v4.30.0
Lean = 4.30.0
focused module build = successful
axioms = [propext, Classical.choice, Quot.sound]
```

This artifact proves only membership and a real-part upper adapter. It does
not prove that the upper is negative, does not provide the other 40959 cell
values or derivative bounds, and does not close the full-line tail or B5
readback.
