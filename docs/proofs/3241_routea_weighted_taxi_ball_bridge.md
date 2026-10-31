# 3241: reusable weighted taxi-ball bridge

Status: Lean-verified reusable component interface; no aggregate sign claim.

Record 3239 proved the weighted original-function enclosure only for the
specific midpoint index 17168. Record 3241 extracts the index-independent
part into two theorems:

- weighted_owner_taxi_ball_mem_of_component_balls3241
- weighted_owner_value_upper_of_component_balls3241

The input consists of two component certificates:

```text
weightBall.Mem (exp (sigma * x))
aggregateBall.Mem (externalPhysical2344 ... x)
             |
             v
(weightBall.mul aggregateBall).Mem (weightedFunction2348 ... x)
             |
             v
weightedExternal3201 ... x <= center.re + radius
```

This preserves the shared complex enclosure through multiplication and only
projects to a real upper at the final step. It does not import numerical JSON,
does not prove a negative value, and does not prove the finite aggregate.

The concrete theorem
record2680_middle_point_weighted_value_upper_via_bridge3241
reinstantiates the interface with the existing 3239 weight ball and 3236
same-owner aggregate ball. The 3240 aggregate adapter now calls this concrete
bridge theorem, so the aggregate route depends on the reusable interface
rather than the duplicated fixed-point projection.

Verification used Linux-native WSL2 ext4 with lean-toolchain
leanprover/lean4:v4.30.0 and Lean 4.30.0. The focused 3241 build and the
3240 rebuild succeeded. Axioms for the two generic bridge theorems, the
concrete reuse theorem, and the 3240 aggregate theorem are exactly
[propext, Classical.choice, Quot.sound].

This reduces the next cell work to constructing phase, bump, and weight balls
for a cell; it does not reduce the number of remaining cells by itself. The
40954 midpoint value certificates, strict finite aggregate inequality,
same-owner full-line tail, and exact B5 readback remain open.The file also provides the cell-facing facade
`weighted_owner_value_upper_of_component_members3241`. A caller supplies one
weight ball and two family-indexed ball functions, together with the weight,
bump, and phase membership proofs. The theorem constructs the 30-family
aggregate ball and returns the weighted real-part upper in one step. This is
the intended interface for replacing one fixed midpoint proof with a family
of cell proofs.The phase constructor `weighted_owner_phase_ball3241` and membership theorem
`weighted_owner_phase_ball_mem3241` expose the existing 512-fold phase scaling
for arbitrary family and coordinate x. The only local premise is the explicit
small-angle condition `|(capturedModulations2584 family * x) / 512| <= 1`.
This is still an enclosure interface, not a signed value certificate.The weight constructor is now parameterized as well:
`weighted_owner_weight_ball3241 sigma x` uses the order-30 two-sided Taylor
interval for `exp (sigma * x)`, and
`weighted_owner_weight_ball_mem3241` proves membership whenever
`|sigma * x| <= 1`. Together with the phase constructor, this removes the
fixed midpoint's weight and phase expansions from future cell proofs.