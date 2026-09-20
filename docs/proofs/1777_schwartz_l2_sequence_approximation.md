# 1777 — Sequential Schwartz approximation in L2

Date: 2026-09-21

## Claim

Every element of the global L2 carrier admits a sequence of Schwartz maps
whose canonical L2 representatives converge to it.

## Formal status

`exists_schwartz_l2_tendsto` converts the committed dense-range theorem for
`SchwartzMap.toLpCLM` into an explicit sequence using metric closure and a
geometric error bound.  It is intended to instantiate the complete kernel
readback theorem for arbitrary L2 inputs.

No kernel diagonal estimate, positivity, or RH conclusion is asserted.
