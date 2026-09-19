# Record 1727: first-order regularity of the scattering phase

## Result

The Gamma archimedean factor and its unit-modulus scattering quotient now have
formal first-order real differentiability on the full real frequency axis:

- `differentiable_ccm24ArchimedeanFactor`
- `differentiable_ccm24ArchimedeanScatteringPhase`
- `differentiable_ccm24ArchimedeanScatteringPhase_inverse`

The proof uses the committed `Gammaℝ` definition, nonvanishing on the critical
line, Mathlib's complex Gamma differentiability away from its poles, real
restriction of complex derivatives, and conjugation/division calculus.

The inverse multiplier is the conjugate phase, so its first-order regularity
is obtained from the same real-linear conjugation map.

## Boundary

This is a regularity interface only. It proves no derivative growth bound,
Schwartz-multiplier estimate, integrable kernel diagonal, or S3 square-sum.
The live S3 obligation remains the Hardy-output identification/regularity or
an independent cutoff-uniform kernel-diagonal majorant.

## Acceptance

The paired Audit leaf was built with the focused target wave and completed with
2965 jobs, zero `error:` lines, zero `sorryAx`, and only
`[propext, Classical.choice, Quot.sound]` in the axiom readback.

Classification: FORMAL. RH is not claimed.
