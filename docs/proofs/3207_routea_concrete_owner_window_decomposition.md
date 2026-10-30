# Record 3207: concrete owner window decomposition

Record 3207 specializes the parameterized 3202 window bridge to the actual
Route A owner:

```text
record2680CorrectionCoefficient
        + capturedModulations2584
        |
        v
weightedExternal3201
        |
        v
expanded diagnostic window
        = exact owner-support window
```

The theorem
`intervalIntegral_record2680_weightedExternal_eq_ownerWindow3207` uses the
3206 interval-integrability theorem for the left, inner, and right intervals.
The two outer intervals vanish by the 3201 support theorem, and the adjacent
interval identities then reduce the expanded diagnostic integral to the exact
owner window.

This is the first Lean theorem in the current chain whose parameters are the
concrete record-2680 coefficient vector and the captured modulation vector.
It closes the owner-specific window/readback boundary, but it does not import
the 3204/3205 JSONL rows or prove their per-cell Taylor bounds.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerWindowDecomposition3207`
- focused target built successfully
- audit: `C1RouteAConcreteOwnerWindowDecomposition3207Audit.lean`
- audited theorem axioms: `[propext, Classical.choice, Quot.sound]`

The remaining numerical boundary is unchanged: the external concrete-owner
Taylor-6 JSONL replay is evidence only. A Lean producer still needs a
per-cell certificate whose values and derivative budgets are bound to this
same owner, followed by the full-line signed-tail bridge.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerWindowDecomposition3207.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerWindowDecomposition3207Audit.lean`
- `build-logs/3207_focused_build.log`
- `build-logs/3207_focused_audit.log`
