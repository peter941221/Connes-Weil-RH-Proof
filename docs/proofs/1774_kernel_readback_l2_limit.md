# 1774 — L2-limit kernel readback socket

Date: 2026-09-21

## Claim

For the selected compact root, if an input sequence converges in L2, every
approximant has the honest kernel-row readback almost everywhere, and the row
integrals converge pointwise, then the limiting Plancherel output has the same
kernel-row readback almost everywhere.

## Formal status

`C1G8R3KernelReadbackL2Limit.lean` proves this in two layers. The generic
`ae_eq_of_lp_operator_tendsto_of_ae_readback` extracts an almost-everywhere
convergent subsequence from L2 convergence and uses uniqueness of metric
limits. `sourceKernelReadback_ae_of_l2_limit` then supplies the continuous
root-convolution output convergence automatically.

The specialized theorem `sourceKernelReadback_ae_of_schwartz_l2_limit`
derives each approximant readback from the already-proved Schwartz-core
formula and the canonical `MemLp.toLp` representative equality. Its only
live analytic hypotheses are therefore L2 convergence and pointwise
convergence of the honest rows.

The proof has no sign premise, no positivity premise, and no stored
conclusion. It is an interface for the healthy `CompactLog` S3 consumer.
The remaining analytic obligation is to provide the approximating sequence and
its pointwise row limit, followed by the annular diagonal majorant.
