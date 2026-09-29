# 2253 — Per-node charge split: the uniform budget is falsified, the count-free fallback holds

Date: 2026-09-30

Consumer: the CHARGE side of the 2246 L2 transfer, registered open by 2250
as "per-node charge `<=` uniform per-node budget `tail/62`".

Verdict: **the uniform per-node budget fails by two orders of magnitude at
the only canonical per-node split; the count-side transfer factor
`owner/62` of the 2246 ledger is withdrawn; the count-free Lean fallback
(charge = the full high-shell tail) keeps the item-5 strict signed margin
with `eps0 > 0` at the 2249 certified margin.**

## The split and its numbers

The split is the absolute-value (triangle) decomposition of the binding
channel of the direct-product mass screen (2234/2238/2243 machinery) over
the 30 construction nodes at the `sigma = 1` row:

```text
q_j          outward per-node mass  int e^{x} |beta_j| |f_j''(x)| dx
             on the committed NX=240001 grid (per-node trapezoid panel
             from the 2234 Lipschitz majorants, per-node solve-radius
             share e2_j, sigma cover, 2^-45 float slack)
T_j          4 * mult_2248 * q_j * P   (ledger units)
P            corr_M0 inflated row bound 1196.4645507389077 (2243)
budget       tail / 62 = 78936995.93168184
```

Measured (whole table in the artifact):

```text
max over all 30 nodes      node 0  (target rho):
                           T = 16349469928.137072 = 207.1204982551802 x budget
max over the 21 zero nodes node 15 (gamma = 40.9187190121475):
                           T = 7659318779.441089  =  97.03078624970799 x budget
split total, channel a     83105.25033831398 = 10.45966847551508 x tail
                            (830.8x the screen's base_D2 7945.304436068302)
split total, channel b     306.8419824442985 x tail
zero-node total           6.199637763470248 x tail
```

Controls: the per-node trapezoid panel sum reproduces the 2234 aggregate
(`11693.314770969453` vs `11693.314770969451`), the per-node solve-radius
shares sum to the artifact inflation (`0.15661735075389555` vs
`0.15661735075389552`), and the split total exceeds the screen by the
expected triangle-vs-signed cancellation factors.

## Why this falsifies the transfer reading

The 2246 ledger charged `tail * (owner/62) + known_error`, valid only if
each owner node carries at most the uniform budget `tail/62`. The measured
per-node charges violate that budget at every scale: the single heaviest
zero node alone costs `97 x` the budget (`1.57 x` the whole tail), and the
21 zero nodes together cost `6.20 x` the tail even though their combined
contribution to the screen is (by construction of the screen) at most one
tail. Cancellation is genuinely inter-node, so no per-node cap smaller
than the tail survives at this decomposition; the transfer factor is a
reading that the committed machinery cannot support and is withdrawn from
the ledger.

## The fallback ledger (count-free)

The Lean brick `exists_weightedZeroMeasure_highShell_tsum_bound` bounds the
owner's high-shell weighted tsum directly by `4 * mult * B`, with `B` the
mass-screen constant on the F side - no zero count enters. The (owner/62)
shave was an optional reduction on top of that bound; removing it:

```text
charge = tail + known_error      4894093747.764274 + 74601530.30234718
                               = 4968695278.066621
margin_lo (2249)                1675396046388.2737
reading                         0.0029656840176851677
eps0                            1670427351110.207
```

The previously recorded transfer readings (`0.0012695287356749262` /
`0.0010339516131735035`, 2249) remain correct arithmetic for the withdrawn
factor; the certified ledger is now the fallback row. The fallback uses
strictly fewer unproven inputs than the withdrawn route (it drops the
per-node uniformity hypothesis entirely); both routes share the same
screen-side instantiation of `B`.

## What this closes and what it does not

Closed: the L2 charge-side question, negatively and definitively at the
available decomposition - the uniform per-node budget is not a theorem
about this construction but a false reading, now measured.

Not closed: a cancellation-aware per-node split (should any future route
want the count-side reduction back); the formal assembly of the fallback
(the 2252 Lean brick already carries the arithmetic; the screen-side
instantiation of `B` remains the registered import chain); the
ideal-to-discrete gaps of the L1 enclosure (separate record in this
batch). No producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_pernode_charge_2253.py`
  (recon: `scripts/routea_weighted_zero_pernode_charge_recon_2253.py`);
- artifact: `results/2253_pernode_charge_uniformity.json`;
- inputs: `results/2243_panel_cem_reprice.json`,
  `results/2237_generation_certificate.json`,
  `results/2234_build_cache.npz`,
  `scripts/routea_weighted_zero_direct_product_outward_2234.py`.