# 2255 — The ideal-to-discrete gaps of the L1 enclosure, measured and charged

Date: 2026-09-30

Consumer: the registered ideal-to-discrete gaps of the 2249 L1 enclosure —
GL phi quadrature, the `[-40,40]` window, the trapezoid step, the owner
list, and the float solve.

Verdict: **each refinement-style gap is measured by doubling and charged as
`|delta q| + both E-totals`; the measured total is `6537949.749302972`, and
the gap-adjusted margin keeps the transfer-free item-5 reading at
`0.00296569559081069` with `eps0 = 1670420813160.4578`.**

## The three measured channels

Committed baseline (2249): `q = -1675397327923.575`, `E_total =
1281535.3012791811`, window `[-40,40]`, step `0.02`, `m = 6400`.

```text
channel   refinement                       delta q              E new                 charged gap
quad      m 6400 -> 12800, [-40,40]        -127417.24731445312  1281535.3201478904    2690487.8687415244
window    ring 40 <= |x| <= 80, step .02   -1.8895946191892285e-16  3.013774912233947e-15  1281535.3012791811
step      step 0.02 -> 0.01, m 6400        52.992919921875      1284338.2850831628    2565926.579282266
```

Charging rules: `gap = |delta q| + E_new + E_committed`; the window channel
is `|delta| + E_ring + E_endpoint-correction + E_committed` with the `+-40`
weight correction `1/50 - 1/100` applied explicitly.

## What the numbers say

The window truncation is below the committed error bar: `|g|` at `x = +-40`
is `5.85594003842789e-20`, the whole ring sum is `-1.8895820282216714e-16`
(roundoff floor), and the charged window gap is just the committed
`E_total` — the `[-40,40]` window is exact at the available error budget.

The two numerical refinements move `q` at the `1e-10` relative scale
(quad: `7.6e-11`, step: `3.2e-11` of `|q|`) while both enclosures'
`E_total` sit at `7.6e-07` relative. The error budget dominates every
refinement difference by ~4 orders of magnitude — which is exactly why
each channel is charged as `|delta q| + both E's`, not by the bare
difference.

The charging is deliberately redundant: the committed `E_total` is charged
in all three channels although they share the committed baseline. The
over-charge (~`2.6e6`) is inside the registered slack and never in the
optimistic direction.

## The four registered gaps, resolved

```text
GL phi quadrature   measured, charged (quad channel above)
[-40,40] window     measured, charged (window channel; truncation below E)
trapezoid step      measured, charged (step channel)
owner list          2254 (per-configuration certified screen) + 2247
float solve         2230 convention A + the 2256 stored-operand residual audit
```

Honest scope: these charges are refinement estimates, not analytic error
bounds — they certify that the committed enclosure error budget covers
every measured refinement shift, at the committed operating point.

## Repriced terminal ledger

```text
margin_2249                     1675396046388.2737
total gap charged               6537949.749302972
margin, gap-adjusted            1675389508438.5244
charge (full tail + known)      4968695278.066621
reading                         0.00296569559081069
eps0                            1670420813160.4578
```

## Nonclaims

No producer GO, no gate sign change, no RH claim. The refine-to-charge
conversions are estimates; an analytic derivation of each gap term
remains a separate obligation if any future consumer needs charging
without the machine experiments.

## Provenance

- script: `scripts/routea_weighted_zero_l1_gaps_2255.py`;
- artifact: `results/2255_l1_gaps.json`
  (md5 `84a1b80ff00e538c2832a1a5ba797ef6`);
- machinery: `scripts/routea_weighted_zero_l1_enclosure_2249.py` (same
  code path, CHUNK changes only grid chunking);
- baseline artifact: `results/2249_l1_enclosure.json`.