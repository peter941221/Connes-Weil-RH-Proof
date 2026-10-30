# Record 3206: owner weighted interval integrability

The weighted external owner function used by the 3201/3202 window bridge is
now proved interval-integrable for arbitrary real endpoints.

The proof has three steps:

```text
weightedExternal3201
        = real part of weightedPhysical2539
        |
        v
weightedPhysical2539 is ContDiff on R
        |
        v
weightedExternal3201 is continuous
        |
        v
intervalIntegral is integrable on every finite interval
```

The proof is concrete at the function level but parameterized over `sigma`,
coefficients, and modulations. It therefore supplies the three explicit
`IntervalIntegrable` premises required by Record 3202 without importing any
numerical JSONL row.

While rebuilding this target, the existing sixth-order derivative extension
exposed an old four-order boundary in the 2536/2537/2538 weighted-family
envelope chain. The local envelope now covers orders 0 through 6, including
the fifth- and sixth-order numerator absolute-value bounds; the existing
lower-order behavior is unchanged.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAOwnerWeightedIntervalIntegrable3206`
- focused target built successfully
- audit: `C1RouteAOwnerWeightedIntervalIntegrable3206Audit.lean`
- audited axioms for all three declarations:
  `[propext, Classical.choice, Quot.sound]`

This closes only the analytic integrability premise for the finite-window
decomposition. It does not consume the 3204/3205 JSONL, prove the per-cell
Taylor bounds, close the full-line tail, establish SourceRH, or establish RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteACoupledBumpEnvelope2536.lean`
- `ConnesWeilRH/Dev/C1RouteAWeightedFamilyLocal2537.lean`
- `ConnesWeilRH/Dev/C1RouteAWeightedFamilyCell2538.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerWeightedIntervalIntegrable3206.lean`
- `ConnesWeilRH/Dev/C1RouteAOwnerWeightedIntervalIntegrable3206Audit.lean`
- `build-logs/3206_focused_build.log`
- `build-logs/3206_focused_audit.log`
