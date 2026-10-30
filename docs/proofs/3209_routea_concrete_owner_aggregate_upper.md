# Record 3209: concrete owner aggregate upper

Record 3209 connects the 3208 per-cell theorem to the finite-partition
aggregator from 3198.

```text
per-cell owner bounds
        |
        v
3208 Taylor-6 cell upper
        |
        v
3198 adjacent-interval sum
        |
        v
concrete owner finite-window upper
```

The theorem `intervalIntegral_record2680_aggregate_upper3209` accepts a grid,
cell centers, value/second/fourth derivative upper arrays, and sixth-derivative
bound array. It proves interval integrability directly from 3206, derives each
cell integral upper from 3208, and sums the results using 3198.

This closes the formal composition boundary from one concrete-owner cell to a
finite window. It does not yet prove the arrays of numeric bounds, consume
the 3204/3205 JSONL, or establish the full-line tail.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateUpper3209`
- focused target built successfully
- audited theorem axioms: `[propext, Classical.choice, Quot.sound]`

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerAggregateUpper3209.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerAggregateUpper3209Audit.lean`
- `build-logs/3209_focused_build.log`
- `build-logs/3209_focused_audit.log`
