# Record 3211: concrete owner global aggregate upper

Record 3211 packages the concrete-owner finite-window aggregate using the
same derivative representation as the 3204/3205 rows:

```text
global midpoint jets
        |
        v
3210 within-cell conversion
        |
        v
3208 cell upper
        |
        v
3198 aggregate
```

The theorem accepts arrays of global value, second-derivative, fourth-
derivative, and sixth-derivative bounds. It proves the finite-window upper for
the same `record2680CorrectionCoefficient` owner and captured modulations.

The remaining work is now numeric proof construction: establish those arrays
in Lean or through a separately verified exact interval-arithmetic certificate.
The external JSONL remains diagnostic input and is not silently imported as a
theorem premise.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerGlobalAggregateUpper3211`
- focused target built successfully
- audited theorem axioms: `[propext, Classical.choice, Quot.sound]`

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalAggregateUpper3211.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerGlobalAggregateUpper3211Audit.lean`
- `build-logs/3211_focused_build.log`
- `build-logs/3211_focused_audit.log`
