# 3229: Route-A reusable family-4 interior midpoint value

Status: verified signed midpoint upper for the genuine interior indices
`40956` and `40957`.

This record extracts the reusable proof kernel used by the right-edge family-4
band. Given exact family-4 support reduction, a strictly negative real upper
for the coefficient-phase product, and positive bump support, it proves the
weighted midpoint upper is nonpositive. It then instantiates that kernel at
`record2680Center3212 40956` and `record2680Center3212 40957`.

The phase box is widened to `[0.8, 1] x [0.2, 0.5]` because repeated
axis-aligned interval squaring widens the formal enclosure even though the
actual phase remains in the narrower diagnostic box. The wider box still
gives a strict negative coefficient-phase real upper.

This closes three adjacent interior entries, `40956`, `40957`, and `40958`, but not the
full interior value array or the finite signed aggregate. The full-line tail,
`producer_go`, `SourceRH`, and RH remain open.

Verification: WSL2 ext4, project toolchain `leanprover/lean4:v4.30.0`, Lean
`4.30.0`, focused build and axioms audit. The audit must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```
