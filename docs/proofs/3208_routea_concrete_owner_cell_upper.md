# Record 3208: concrete owner cell upper

Record 3208 creates the per-cell Lean interface for the concrete owner
`record2680CorrectionCoefficient` with `capturedModulations2584`.

For one cell `[left, right]` with midpoint `center`, the theorem accepts:

- an upper bound for the owner function at `center`;
- an upper bound for the within-cell second derivative;
- an upper bound for the within-cell fourth derivative;
- a nonnegative uniform sixth-derivative bound;
- the exact midpoint relation and interval ordering.

It then applies the proved Taylor-6 integral bridge from 3197 and returns the
cell integral upper with the exact coefficients `1/24`, `1/1920`, and
`1/322560`.

The numeric bounds remain explicit premises. This is deliberate: a JSONL row
is a serialized diagnostic, not a Lean proof. The next proof obligation is to
prove those premises for the same concrete owner and each grid cell.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellUpper3208`
- focused target built successfully
- audited declarations use exactly `[propext, Classical.choice, Quot.sound]`

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerCellUpper3208.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerCellUpper3208Audit.lean`
- `build-logs/3208_focused_build.log`
- `build-logs/3208_focused_audit.log`
