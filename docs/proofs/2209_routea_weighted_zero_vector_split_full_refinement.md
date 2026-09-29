# 2209 — Full-owner NSEG=1100 vector-split refinement

Date: 2026-09-29

The vector-aware endpoint-split rule was rerun for all 30 owner nodes and all
30 family functions at `NSEG=1100`.

```text
rhs          worst node   max bound
base              29      6.2349677e-08
correction         2      4.9348931e-05
```

The minimum bounds over all nodes were `4.2682e-9` for base and `1.3222e-8`
for correction; no hidden node exceeded the binding rows already found in
2208. This is the full-node numerical refinement corresponding to the binding
screen, not yet an outward certificate.

Status: `VECTOR-SPLIT-FULL-NSEG1100 / ALLOWANCE-PENDING`.

*** Add File: C:\Projects\Connes-Weil-RH-Proof\docs\proofs\2210_routea_weighted_zero_vector_rounding_allowance.md
# 2210 — NSEG=1100 rounding allowance

Date: 2026-09-29

The correction binding row's forward-rounding price was recomputed at the same
`NSEG=1100` rule as 2209.

```text
GL allowance                         7.8069841e-6
Simpson allowance                    5.3698068e-6
coefficient rounding                 6.7767136e-12
total allowance                      1.3176798e-5
```

Combining this with the 2209 correction bound gives approximately
`6.253e-5`, or about `7.44e-5` relative movement after the 2201 inverse-norm
propagation. Thus the measured rounding price remains below the earlier
`1e-4` screen.

Status: `VECTOR-SPLIT-ROUNDING-ALLOWANCE-PRICED / ANALYTIC-ALLOWANCE-OPEN`.

The term sums are still floating measurements and no transcendental interval
bound or complete-owner transfer has been proved. No producer theorem or RH
claim follows.

