# 3198 Route A Cell-Upper Aggregate

Status: finite cell upper aggregation is verified in Lean.

The theorem `intervalIntegral_le_sum_cell_upper3198` takes a grid, one upper
bound per cell, interval-integrability for every adjacent cell, and a proof of
the integral upper bound for every cell. It then uses Mathlib's adjacent
interval identity to prove the whole-window bound.

```text
cell 0 upper proof  --+
cell 1 upper proof  --+--> sum of cell uppers
...                 --+          |
cell N-1 upper proof--+          v
                              whole-window upper
```

The theorem deliberately does not accept raw JSON or numerical strings as
proofs. The 3187 JSONL sidecar is therefore an external candidate input; each
row still needs an owner-specific proof, or a generated Lean certificate whose
proof fields are checked against the same `correctedPhysical` object.

Evidence:

- `build-logs/3198_wsl_build.log`
- `build-logs/3198_wsl_audit.log`

The audit reports exactly `[propext, Classical.choice, Quot.sound]`.
