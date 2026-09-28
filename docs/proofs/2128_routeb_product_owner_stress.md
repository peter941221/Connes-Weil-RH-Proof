# 2128 — Fixed-n full-product owner-cardinality stress

Date: 2026-09-28.

Status: SCOPED-NO-GO-FOR-FIXED-N6-FULL-PRODUCT. This is a reproducible
numerical stress result, not a theorem about the formal source-zero set.

## Consumer and mechanism

The consumer is the same-owner phase-balanced gate for the `n = 6` row. The
mechanism tested is the formal full-product idea: source-zero nodes carry zero
interpolation values, so owner cardinality enters through the product factor
rather than through one nonzero basis coefficient per node.

The test keeps the same `rho`, support radius 16, powered seed, `q = 2^-14`,
595877-prime book, and fixed `n = 6`. It adds synthetic critical-line nodes
inside the closed ball, all with zero interpolation values.

## Result

At `dxi = 0.05`:

```text
extra nodes   total owner   C              b              det              gate
0             40            +1.822e7       +3.037e10      -4.981e21         PASS
40            80            -5.586e9       -3.843e13      +2.955e25         FAIL
80            120           +1.420e21      +4.070e24      +6.064e46         FAIL
160           200           NaN            NaN            NaN                FAIL
320           360           NaN            NaN            NaN                FAIL
```

The correction maximum grows from `1.07e2` at 40 nodes to `5.01e13` at 80
nodes and `6.77e54` at 120 nodes. The fixed-n product mechanism therefore
cannot be promoted by simply replacing the known-zero prefix with a larger
formal owner.

## Scope and next move

This does not rule out support-growing constructions with a changed
`orbitIndex`, nor does it claim the synthetic nodes are zeta zeros. It does
rule out spending more time on the unchanged `n = 6` full-product route.
The mechanism screen fires the gate/tail-index and error-gap antibodies; the
next admissible work must change the named mechanism or prove a new owner-local
signed bound.

## Reproducibility

```text
python3 scripts/routeb_product_owner_stress_2128.py
```

Artifact: `results/2128_routeb_product_owner_stress.json`.