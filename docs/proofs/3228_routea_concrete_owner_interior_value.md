# 3228: Route-A concrete-owner interior midpoint value

Status: verified signed midpoint upper for the genuine interior index `40958`.

The proof uses the exact `record2680` owner definition. It proves that the
midpoint at index `40958` is supported only by family 4, transfers the exact
phase into a rational coarse rectangle, proves the family-4 coefficient-phase
real upper is strictly negative, and uses positive bump and exponential
factors to derive:

```text
weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
  capturedModulations2584 (record2680Center3212 40958) <= 0
```

This is a signed proof, not a support-zero claim. Index `40958` is interior,
so it reduces the remaining value premise in 3227 by one genuine interior
cell. It does not close the full interior value array, the finite signed
aggregate, the full-line tail, `producer_go`, `SourceRH`, or RH.

Verification: WSL2 ext4, project toolchain `leanprover/lean4:v4.30.0`, Lean
`4.30.0`, focused build and axioms audit. The audit must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```
