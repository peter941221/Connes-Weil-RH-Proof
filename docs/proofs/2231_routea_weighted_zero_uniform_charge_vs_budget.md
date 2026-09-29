# 2231 — Uniform charge vs candidate budget

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

This record prices ladder item 3 of the q-construction terminal: one uniform
charge, the maximum over the 30 owner nodes of the outward 2229 envelope,
against the candidate budget chain already on the shelf. The comparison is
arithmetic over committed artifacts; it adds no numeric claim of its own.

## The numbers

```text
uniform charge (max over nodes)   8.792971355816406e-09    node 2
min node charge                   4.441432860466601e-09    node 1
max / min                         1.9797600531312878
2211/2217 combined-correction target        6.2550323e-05   (absolute)
uniform charge / target                     1.4057435572021598e-04
2223 MPFR implementation price              7.039855400051501e-12
assembled replay (uniform + 2223)           8.800011211216458e-09
assembled / target                          1.4068690278731986e-04
2217 parameterized AMP price (binding node) 2.459424789942387e-08
AMP price / uniform charge                               2.7970349162067016
2197 signed-margin anchor                   1.675397327895099e12
uniform charge / anchor                     5.248290187297563e-21
```

The 2224 assembly of the same quantity used the parameterized 2217 term and
read `3.933039283398092e-04` of the target. Replacing that term by the
outward 2229 charge lowers the binding-node assembled reading by a factor
`2.7956`, from `3.9330e-04` to `1.4069e-04` of the target.

Drift control (2228 in-process vs 2229 outward, all outward, at the binary64
rounding level):

```text
node 2   +8.43769498715119e-15 relative
node 3   +7.993605777301127e-15 relative
node 29  +5.551115123125783e-15 relative
```

## What this closes and what it does not

The uniform charge is the exponent-argument propagation: under the
discrete-defined operand convention (2230) it bounds, for every node, the
deviation `|exp(q_exact) - exp(q_float)|` summed with the `|c||w|` weights
over the full 1,944,360-term rule, in directed MPFR arithmetic. The 2223
term separately covers the certified library implementation radius of
`exp`/`sin`/`cos`. Together they replace the 2217 parameterized forward-error
price in the 2224 assembly with an outward reading `2.797 x` tighter.

Not closed by this number:

- the remaining components of the `6.2550323e-05` combined price are
  unchanged; record 2211 states the Simpson fourth-order remainder is the
  binding part of that total, and 2231 does not reprice it;
- the binary64 operand construction ledger (coefficient solve, quadrature
  generation error) of 2230 item 2a;
- the family-stitch formalization of 2229;
- the low-shell/`B_zm` side and complete-owner transfer;
- the strict signed producer margin.

The ratio to the 2197 signed-margin anchor is listed only to keep the two
channels visible in one place; the uniform charge is an absolute error
quantity and the anchor is a signed margin, so the quotient is bookkeeping,
not a margin consumption.

## Status

`UNIFORM-CHARGE-PRICED`. Ladder item 3 of the q-construction terminal is
priced: one uniform charge `8.792971355816406e-09` covers all 30 owner nodes
at zero interval failures, and it consumes `1.4069e-04` of the candidate
correction target when assembled with the certified implementation price.
No producer or RH claim follows.

Artifacts:

- `results/2231_uniform_charge_vs_budget.json`
- `results/2229_q_mpfr_all_nodes.json` (source of the charges)
- script: `scripts/routea_weighted_zero_uniform_charge_budget_2231.py`
- inputs: `results/2217_weighted_zero_ieee_radius.json`,
  `results/2223_mpfr_exp_binding.json`,
  `results/2228_q_mpfr_node{2,3,29}.json`