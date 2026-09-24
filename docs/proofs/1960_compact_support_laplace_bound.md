# Proof Record 1960: compact-support Laplace envelope

## Result

Added `ConnesWeilRH/Dev/C1CompactSupportLaplaceBounds.lean` with the theorem
`norm_laplaceAt_le_exp_mul_l1Mass` in the existing
`CC20YoshidaCriticalContraction.CompactLogTest` namespace.

For a compact logarithmic test `f` supported in `[-B, B]`, the theorem proves

```text
norm(laplaceAt(f, s)) <= exp(abs(Re(s)) * B) * l1Mass(f)
```

The proof uses only the pointwise support bound, the norm of the complex
exponential, and `norm_integral_le_integral_norm`. It does not assume a sign
for the Laplace value or a numerical formula for the Mathlib bump.

## Verification

Focused WSL build in a WSL ext4 verification copy:

```text
lake build ConnesWeilRH.Dev.C1CompactSupportLaplaceBounds
lake build ConnesWeilRH.Dev.C1CompactSupportLaplaceBoundsAudit
```

Batch verification of the seven new `C1` Dev leaves and their paired audits
(2026-09-24) reports footer `Build completed successfully (3651 jobs)`, zero
`error:` lines, and 35 `#print axioms` lines, all exactly:

```text
[propext, Classical.choice, Quot.sound]
```

with no `sorryAx`.

## Map 106 impact

This removes one analytic wrapper obligation for the explicit finite-node
correction: every correction term can now be bounded after supplying its
support radius and `L¹` mass. The remaining quantitative work is still the
actual mass/node-product bound and the signed gate determinant for the same
owner. This record therefore does not claim `det < 0`, a producer witness, or
RH.

The full aggregate build remains independently blocked by the pre-existing
`ConnesWeilRH.Source.CC20Concrete.HaarMellinMismatch` target; that failure is
not caused by this theorem.