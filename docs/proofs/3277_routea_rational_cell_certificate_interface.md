# 3277 Route A rational cell certificate interface

## Result

This record closes the formal interface between per-cell rational interval
certificates and the existing 40960-cell Taylor-6 aggregate theorem.  It does
not claim that the numeric certificates have been generated or proved.

```text
rational weight interval + 30 rational family rectangles
                         |
                         v
              generic interval membership
                         |
                         v
                 midpoint upper (`hvalue`)
                         |
                         v
              existing 40960-cell Taylor aggregate
```

## Formal boundary

`C1RouteARationalCellCertificates3277.lean` defines:

- `ratCellValueUpper3277`: the real upper endpoint after multiplying the
  rational weight rectangle by the rational aggregate rectangle.
- `ratCellValueUpper3277_spec`: generic weighted midpoint upper bound.
- `ratCellValueUpper3277_family_spec`: the same bound after the 30-family
  finite-sum bridge.
- `record2680_40960_midpoint_upper_of_rat_cell_certificates3277`: converts
  per-cell containment hypotheses into the required `hvalue` function.
- `intervalIntegral_record2680_40960_global_aggregate_upper_of_rat_cell_certificates3277`:
  supplies that `hvalue` to the existing Taylor-6 aggregate theorem.

The certificate hypotheses remain explicit.  This is intentional: a sidecar
file can provide candidate endpoints, but only a Lean proof of each weight and
family containment premise can enter the formal aggregate.

## Verification

The focused build was run in the Linux-native WSL2 ext4 workspace after
checking `lean-toolchain` and `lean --version`.  The required toolchain was
`leanprover/lean4:v4.30.0`, with Lean `4.30.0`.  The audit file reports only:

```text
[propext, Classical.choice, Quot.sound]
```

The remaining work is to prove the actual rational weight, phase, bump, and
family endpoint premises for all 40960 cells.  This record does not prove
`SourceRH`, `producer_go`, or RH.
