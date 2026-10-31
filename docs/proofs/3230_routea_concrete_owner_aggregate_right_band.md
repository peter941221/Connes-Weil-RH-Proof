# 3230: Route-A aggregate adapter with the verified right band

Status: verified aggregate adapter.

The adapter wires the signed midpoint proofs for indices `40956`, `40957`,
and `40958`, together with the endpoint proofs for `0` and `40959`, into the
cell-local Taylor aggregate. Those five entries use the certified upper `0`.
The remaining value premise is required only for indices outside:

```text
{0, 40956, 40957, 40958, 40959}
```

This is an interface reduction, not yet a negative finite aggregate. The
remaining midpoint array, aggregate sign, full-line tail, `producer_go`,
`SourceRH`, and RH remain open.

Verification: WSL2 ext4, project toolchain `leanprover/lean4:v4.30.0`, Lean
`4.30.0`, focused build and axioms audit. The audit must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```
