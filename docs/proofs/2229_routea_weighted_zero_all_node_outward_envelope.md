# 2229 — All-30-node outward q-interval envelope

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

This record executes ladder item 1 of the q-construction terminal: the
corrected 2225/2228 q-interval evaluator is extended to every one of the 30
owner nodes, and the propagated exponent-radius charge is upgraded from
binary64 nearest-rounding accumulation (2225/2228) to MPFR directed-upward
accumulation. It does not touch the owner, the quadrature rule, or the
signed producer margin.

## What changed and why

The 2225/2228 accumulation `total_charge += abs(c)*abs(w)*bound` was already
outward per term (`bound` is `nextafter`-inflated), but the binary64
nearest-rounding sum is not an outward operation. Record 2229 replaces the
whole per-term chain with directed MPFR arithmetic:

```text
delta  = nextafter-up(rr + ri)                    (radius sum, up)
exp    = mpfr_exp(qr, RNDU)                       (256-bit, up)
bound  = 2*delta*exp        for delta < 1         (Lean 2212/2213 form)
       = exp(delta)*exp      otherwise            (all-delta form)
term   = mpfr_mul(mpfr_mul(exp, bound, RNDU), cabs, RNDU), then wabs
accum  = mpfr_add(acc, acc, term, RNDU)           (per-family accumulators)
```

The Simpson panel factor `(hi - lo)/(2*NSEG)/3` is inflated by 4 binary64
steps before the directed products. Every binary64 operand handed to MPFR
(`qr`, `cabs`, `wabs`, `delta`, the panel factor) is exact under the
discrete-defined operand convention recorded in 2230.

Two honest limits remain in the artifact's nonclaims:

- the binary64 operands are taken as exact (convention A of 2230);
- the 30 family totals are stitched in binary64 with upward inflation
  (`total = nextafter-up(total + gl + sim)`). Two half-spacing roundings
  down plus one `nextafter` up make the stitch outward to first order; the
  artifact states this as a nonclaim rather than a proof, and a one-line
  strengthening (three-step up-inflation or MPFR family accumulation) is
  queued for the successor record.

## Operand pin and drift control

The node-independent setup (node list, coefficient solve, 30 quadrature
grids) is built once by `MODE=build` and pinned:

```text
results/2229_operand_cache.npz   md5 c78a0342fad8ac0166c23d01f653f666
size 18434906 bytes              call chain identical to the 2225 evaluator
```

Smoke control against the 2228 in-process readings (outward, as designed):

```text
node 2   cache smoke family 0   3.60315281153439503e-09
         2228 family 0          3.603152811534377e-09     +5.0e-16 relative
```

## Result

30 nodes, 30 families each, `NSEG=1100`, 12 Simpson panels, 1,944,360 terms
per node, zero interval failures at every node:

```text
node   charge            node   charge            node   charge
 0     4.741900e-09       10    5.078149e-09       20    5.360926e-09
 1     4.441433e-09       11    5.030699e-09       21    5.490735e-09
 2     8.792971e-09       12    4.900040e-09       22    5.573892e-09
 3     8.063939e-09       13    4.763836e-09       23    5.755320e-09
 4     5.171385e-09       14    4.556201e-09       24    5.726350e-09
 5     6.360731e-09       15    4.558776e-09       25    5.739474e-09
 6     6.789402e-09       16    4.674708e-09       26    6.087836e-09
 7     7.571867e-09       17    4.885994e-09       27    6.196423e-09
 8     5.630892e-09       18    4.967670e-09       28    6.222831e-09
 9     5.376133e-09       19    5.128952e-09       29    6.475830e-09
```

Full-precision readings:

```text
worst node 2    8.792971355816406e-09
min   node 1    4.441432860466601e-09     max/min 1.9797600531312878
node 3          8.06393863291298e-09
node 29         6.475830084303264e-09
```

Drift control against the 2228 in-process readings, all outward and at the
binary64 rounding level:

```text
node 2   8.792971355816332e-09 -> 8.792971355816406e-09   +8.4377e-15 rel
node 3   8.063938632912915e-09 -> 8.06393863291298e-09    +7.9936e-15 rel
node 29  6.475830084303228e-09 -> 6.475830084303264e-09   +5.5511e-15 rel
```

The 2217 full-node forward-error screen had its maximum at node 2 as well
(`2.459424789942387e-08`), so the binding node is stable across both the
parameterized price and the outward certificate. The outward reading is
`2.797 x` smaller than that parameterized price.

## Status

`MPFR-Q-INTERVAL-ALL-NODE-OUTWARD`. Ladder item 1 of the q-construction
terminal is executed. Inside the discrete-defined operand convention the
30-node exponent-radius charge is now an outward quantity with zero interval
failures.

Still open, and listed in the artifact's nonclaims: the binary64 operand
construction ledger (coefficient solve, quadrature generation error,
record 2230 item 2a), the family-stitch formalization, the low-shell/`B_zm`
side, complete-owner transfer, and the strict signed producer margin. No
producer or RH claim follows.

Artifacts:

- `results/2229_q_mpfr_node0.json` ... `results/2229_q_mpfr_node29.json`
- `results/2229_q_mpfr_all_nodes.json`
- `results/2229_operand_cache.npz` (local pin, md5 above, not committed)
- script: `scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py`