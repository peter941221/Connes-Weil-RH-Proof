# Record 1175 — P2 kernel-compatibility consumer

Date: 2026-09-06

## Result

`tendsto_norm_cutoffKernelInsertionSandwich_zero_of_kernelCompatibility`
consumes the named proposition `kernelCompatibilityAlongCutoffs` and returns
operator-norm convergence of the first projection defect
`cutoffKernelInsertionSandwich g lambda S n` to zero.  It is a direct
composition with the existing quantitative sandwich theorem.

## Boundary

The theorem does not prove the compressed-kernel estimate.  It adds no decay,
limit, arithmetic readback, positivity, or RH conclusion; the compatibility
proposition remains an explicit producer obligation.  The focused owner/probe
build completed successfully in 3821 jobs, with no `error:` lines or `sorryAx`;
the audit output uses only `[propext, Classical.choice, Quot.sound]`.
