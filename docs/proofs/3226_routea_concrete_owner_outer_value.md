# 3226: Route A concrete-owner outer midpoint value

Status: verified signed midpoint upper.

The theorem mirrors the 3218 phase-scaling proof at the positive outer
midpoint `index = 40959`. Lean proves:

```text
only family 4 survives exact support reduction
phase / 512 lies in the small-angle domain
512th-power phase lies in a positive-imaginary coarse rectangle
coefficient-phase real upper is strictly negative
bump is strictly positive because the midpoint is inside support
weighted midpoint value <= 0
```

The exported theorem is:

```text
record2680_last_center_weighted_value_upper3226
```

The focused WSL2 Lean `4.30.0` build and axioms audit pass with exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This is a signed proof, not a support-zero shortcut.
