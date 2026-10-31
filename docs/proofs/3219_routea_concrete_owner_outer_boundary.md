3219 Route-A Concrete-Owner Outer Boundary
==========================================

Lean proves that the final diagnostic midpoint, index 40959, still satisfies
`|record2680Center3212 40959| < storedWidth 4 ^ 2` for the selected owner.
Therefore its `value_upper = 0` diagnostic row cannot be justified by a
support-zero identity. The outer cell remains a signed Taylor cell and must be
handled by the same-owner value and derivative arrays.

Verification
------------

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerOuterBoundary3219`
- axioms: `[propext, Classical.choice, Quot.sound]`