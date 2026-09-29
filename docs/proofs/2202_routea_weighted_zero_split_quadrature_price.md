# 2202 — Endpoint-split quadrature price and scoped solve no-go

Date: 2026-09-29

This probe targets the active same-owner Route-A consumer

```text
actual source owner -> same-owner qw >= 0 -> SourceRH -> Mathlib RH.
```

It replaces the invalid idea of an ellipse estimate through the Gevrey bump's
outer endpoint by the split estimate

```text
|GL-I| <= |GL-S_inner| + |S_inner-I_inner| + |GL_edge| + |I_edge|.
```

The inner interval uses composite Simpson and an explicit fourth-derivative
bound for `exp(-K/(1-u^2) + z x)`. The two edge intervals use the concave
maximum of the real exponent and a direct length-times-maximum bound.

## Run

The 30-node owner, `m=6400`, `delta_u=0.05`, 12 inner panels, and 20 Simpson
half-panels per inner panel were evaluated by
`scripts/routea_weighted_zero_split_quadrature_price_2202.py`.

The resource-aware run completed successfully. The artifact is
`results/2202_weighted_zero_split_quadrature_price.json` and the log is
`results/20260929_2202_split_quadrature_price_pass2.log`.

```text
max entrywise error price       2.7215087982893587e-14
argmax family                   3 (a=2.32, theta=39.25244858548658)
owner matrix dimension          30
```

Using the entrywise maximum as a row-sum bound gives
`||E||inf <= 30 * 2.7215e-14 = 8.1645e-13`. Combined with the solve control
from 2201, `||A0^-1||inf = 6.7705e17`, the Neumann factor is at most about
`5.53e5`, so this bound cannot close the solution enclosure.

## Decision

`ENTRYWISE-SPLIT-BOUND-NO-GO` for this resolution and assembly. The result is
scoped: it does not rule out the direct-product mechanism, nor every endpoint
split rule. It rules out feeding this componentwise-modulus Simpson price
directly into the ill-conditioned 30-by-30 solve.

The admissible next designs must either preserve matrix-level cancellation
before taking moduli, substantially sharpen the inner quadrature rule, or use a
different solve enclosure. No producer theorem or RH claim follows.

