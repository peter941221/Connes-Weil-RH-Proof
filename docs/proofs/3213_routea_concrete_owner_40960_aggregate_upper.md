# Record 3213: concrete owner 40960-cell aggregate interface

Record 3213 specializes 3211 to the fixed 40960-cell diagnostic grid from
3212. The theorem now accepts only the owner-specific value, global second,
global fourth, and sixth-derivative bound arrays.

```text
fixed 40960 grid geometry
        |
        v
3212 endpoint/order/midpoint proofs
        |
        v
3213 finite-window aggregate theorem
```

This is the final formal interface before numeric certificate construction.
The JSONL remains external evidence; its serialized numbers still require
independent Lean-verifiable bounds before they can be supplied to 3213.

Verification:

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwner40960AggregateUpper3213`
- focused target built successfully
- audited theorem axioms: `[propext, Classical.choice, Quot.sound]`

Evidence:

- `ConnesWeilRH/Dev/C1RouteAConcreteOwner40960AggregateUpper3213.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwner40960AggregateUpper3213Audit.lean`
- `build-logs/3213_focused_build.log`
- `build-logs/3213_focused_audit.log`
