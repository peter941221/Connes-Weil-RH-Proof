# Record 3212: concrete owner 40960-cell grid

Record 3212 formalizes the exact uniform grid used by the 3204/3205
diagnostic: 40960 cells over
`[-diagnosticRadius3201, diagnosticRadius3201]`.

Lean proves the left endpoint, right endpoint, strict ordering of every
adjacent pair, and the midpoint identity. The strict ordering proof is
important because 3210 needs the midpoint to lie in the open interior of each
cell before converting global jets to within-cell jets.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerGrid3212`
- focused target built successfully
- audited declarations use exactly `[propext, Classical.choice, Quot.sound]`

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGrid3212.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGrid3212Audit.lean`
- `build-logs/3212_focused_build.log`
- `build-logs/3212_focused_audit.log`
