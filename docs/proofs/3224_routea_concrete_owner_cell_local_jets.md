# 3224: Route A concrete-owner cell-local jet bounds

Status: verified cell-local second/fourth bounds.

The theorem uses the actual diagnostic cell endpoints and the existing
`cellNearAbs2538` / `cellAbs_le_max2538` geometry. A family is handled in one
of two ways:

```text
cell crosses family support and midpoint is inside
    -> apply the local 2538 derivative envelope

midpoint is outside family support
    -> use the exact derivative-zero theorem
```

This distinction is essential. A cell can cross a family support boundary
while its midpoint is already outside that family support.

Exported midpoint bounds:

```text
record2680_cell_second_bound3224
record2680_cell_fourth_bound3224
```

Both are same-owner Lean theorems for every `index < 40960`; no diagnostic
JSONL row is imported. The focused WSL2 Lean `4.30.0` build and axioms audit
pass with exactly:

```text
[propext, Classical.choice, Quot.sound]
```
