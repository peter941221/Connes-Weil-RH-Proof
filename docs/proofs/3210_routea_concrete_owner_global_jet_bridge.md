# Record 3210: concrete owner global-jet bridge

The 3204/3205 diagnostic rows store global second and fourth derivatives at
cell midpoints. The 3208 Taylor interface uses `iteratedDerivWithin`, because
the Taylor theorem is stated on the cell. Record 3210 proves these quantities
are equal when the midpoint is strictly inside the cell.

It also provides a cell-upper wrapper that accepts the global second/fourth
jet bounds directly. The midpoint interior condition is explicit; it is not
inferred from a merely non-strict endpoint relation.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerGlobalJetBridge3210`
- focused target built successfully
- audited declarations use exactly `[propext, Classical.choice, Quot.sound]`

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalJetBridge3210.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalJetBridge3210Audit.lean`
- `build-logs/3210_focused_build.log`
- `build-logs/3210_focused_audit.log`
