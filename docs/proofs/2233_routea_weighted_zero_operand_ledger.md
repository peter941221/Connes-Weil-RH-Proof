# 2233 — Operand construction ledger: c, w and x channels

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Record 2230 defined convention A (the stored binary64 operand tuple
`(K, a, theta, node, x, c, w)` is exact) and left ladder item 2a open: the
ideal-to-stored conversion ledger. This record prices the three channels of
that ledger that are measurable from committed artifacts. All three parts
are screens or provisional prices; none of them is a certificate.

## Part 1 — c channel (coefficient solve)

The q-terminal charge is linear in `|c|`, so a uniform coefficient radius
`r_c` inflates it by at most `r_c * sum_f T_f / charge`, with
`T_f = family_charge / |c_f|`. Using the record-2201 provisional radii on
the 2229 all-node data:

```text
binding node (max charge)              2
|coeff|_min                           88113.48657237015
|coeff|_max                           5.6875117346762605e+17
T-sum at node 2                        charge-weighted, see artifact
2201 radius, base-labeled              1.725905221940381e8
2201 radius, correction-labeled        3.536472115641207e11
inflation (base radius)                5.478274212797956e-09   relative
inflation (correction radius)          1.1225276886070804e-05  relative
```

Cross-identification: `|coeff|_max` here is bitwise the `corr_c_inf` of the
2197 direct-product system (2235): the 2225 q-chain solve and the 2197
direct-product solve are the same 30x30 system with the same right-hand
side, so one coefficient vector serves both consumers.

The same 2201 radius charges very differently in the two consumers: on the
q-chain it costs `1.12e-05` relative (`T_f = charge_f/|c_f|` weights the
large-coefficient families almost to nothing), while on the direct-product
screen it costs `4.76e4` relative (2235/2236 per-unit-coefficient mass
bounds). The radius is one object; the sensitivity is the consumer's.

## Part 2 — w channel (quadrature weight generation)

Screened through the Gauss-Legendre moment identities on the stored grids,
in directed MPFR (RNDU upper, RNDD lower) over all 30 families x 38400
stored nodes:

```text
sum_j W_j          vs 2a
sum_j W_j x_j^2    vs 2a^3/3
sum_j W_j x_j^4    vs 2a^5/5
worst family                           8
worst relative gap                     9.164518758595832e-14
```

A gap of `9.2e-14` relative is consistent with the binary64 generation of
the composite GL grids (38400-term affine maps and weight scalings): the
stored weights deviate from the exact identity values at the `1e-13` level.
The corresponding charge inflation is at most that relative size for the
weight channel and is not separately accumulated here.

## Part 3 — x channel (node generation), sampled

Convention A stores the 38400 x nodes per family; an ideal node differing
by `k` ulps (`k in {1, 16}`) shifts the exponent argument by

```text
|dq| <= |dq/dx| d_k + (1/2)|q''| d_k^2,  d_k = k 2^-52 |x|,
|dq/dx| <= 2K|x|/a^2 (1-u^2)^-2 + |z|,
|q''|   <= (2K/a^2)((1-u^2)^-2 + 4u^2 (1-u^2)^-3).
```

The node-2 and node-1 charges were re-evaluated at the widened radius
`nextafter-up(rr + ri + extra_k)` with MPFR RNDU accumulation, 30 families
each, both the GL grid and the Simpson panels:

```text
node 2 (binding charge)   base drift vs 2229   0.0 (bitwise, all 30 families)
                          k = 1   inflation    +0.15158672812255491
                          k = 16  inflation    +2.4253876499608817
node 1 (minimum charge)   base drift vs 2229   0.0
                          k = 1   inflation    +0.015164728187683663
                          k = 16  inflation    +0.24263565100294815
```

Read into the 2231 budget: a one-ulp node displacement raises the uniform
charge from `8.792971355816406e-09` to `1.0126e-08`, i.e. from
`1.4057e-04` to `1.6187e-04` of the `6.2550323e-05` target — the x channel
costs about `2.1e-05` of the target, still two orders below 1. The
sixteen-ulp reading costs `2.801e-04` of the target and remains affordable.

## What this closes and what it does not

Priced or screened: the coefficient radius channel (provisional),
the weight generation channel (screened, `9.2e-14`), the x-node generation
channel (sampled, one-ulp `+15.2%` on the binding node).

Not closed:

- the c-channel price uses the provisional 2201 radius; 2235/2236 separate
  its generation and solve components and charge the solve floor, but a
  certified solve enclosure is still open;
- the w-channel is screened through moments, not certified per weight; the
  x-channel samples two nodes and states `k` ulps as a model of the
  generation error rather than a bound on it;
- convention A (stored operands exact) remains the certificate reference;
- owner transfer and the signed producer margin remain open;
- no producer or RH claim.

## Provenance

- scripts: `scripts/routea_weighted_zero_operand_ledger_2233.py` (parts 1-2),
  `scripts/routea_weighted_zero_xwidth_charge_2233.py` (part 3, backend
  `scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py`)
- inputs: `results/2229_operand_cache.npz` (md5
  `c78a0342fad8ac0166c23d01f653f666`), `results/2229_q_mpfr_node*.json`
- outputs: `results/2233_operand_ledger.json`,
  `results/2233_xwidth_charge.json`,
  `results/2233x_node{2,1}_fam*_*.json` (60 per-family artifacts)