# 1775 — L2 convergence implies pointwise kernel-row convergence

Date: 2026-09-21

## Claim

For a Schwartz approximation sequence converging in L2 to an arbitrary
`MemLp` input, each translated compact-root kernel row integral converges to
the limiting row integral at every output point.

## Formal status

`sourceKernelRow_integral_tendsto_of_schwartz_l2_tendsto` converts the L2
convergence into convergence of the norm of the input difference, then uses
the existing `frontierLp2normEqIntegralSqrt` and
`frontierLp2normToReal` identities to obtain the exact real Holder majorant.
The earlier Holder-row theorem then gives the pointwise row limit.

This is a formal bridge only: it proves neither the annular kernel-diagonal
bound nor positivity of `qw`.
