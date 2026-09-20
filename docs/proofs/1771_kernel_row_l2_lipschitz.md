# Proof record 1771: pointwise L2 Lipschitz estimate for the kernel row

Date: 2026-09-21

Status: FORMAL, no sign claim.

## Result

`sourceKernelRow_integral_norm_sub_le` proves the fixed-output estimate

`norm(row(u,t) - row(v,t)) <= L2Norm(u-v) * L2Norm(kernel_t)`.

The kernel is certified as a translated/reflected Schwartz function, and the
bound is an explicit application of Holder(2,2).

## Route role

This is the continuity estimate needed to pass the honest row formula from
the Schwartz dense core to arbitrary L2 inputs pointwise in the output
variable.  It does not yet prove that the resulting output function is L2,
nor identify that output with the Plancherel operator without the remaining
global extension argument.

## Provenance

Original project formalization using Mathlib's `MemLp.sub`, translation
invariance, and `integral_mul_norm_le_Lp_mul_Lq`.  No numerical input, new
axiom, or positivity statement is used.
