# 2239 — x-channel charge ledger: all 30 owner nodes

Date: 2026-09-30

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

Verdict: **measured, closed at the model level**. The 2233 x-channel
sweep (one and sixteen ulps of the stored binary64 x node) now covers all
30 owner nodes instead of the two sampled ones. Worst node is 2 at both
levels, so the 2233 headline stands as the all-node worst case, and the
whole ledger re-runs bitwise:

```text
base drift vs committed 2229 charge  0.0 at all 30 nodes (bitwise)
node 2 / node 1 rows                 bitequal to the committed 2233 artifact
worst k1  (one ulp)                  node 2, +15.158672812255491%
worst k16 (sixteen ulps)             node 2, +242.53876499608817%
worst one-ulp absolute charge        1.332898e-09 = 2.1309206641563692e-05 of target
```

The last line is the ledger reading: a one-ulp move of the binding node's
x shifts its q charge by `1.33e-09`, `2.13e-05` of the 2224 target
`6.2550323e-05` — the same number 2233 reported for the binding node, now
confirmed to be the maximum over the full owner set.

## Full ledger (30 nodes)

Columns: base relative drift against the committed node charge; k1/k16
relative inflation of the re-evaluated charge; one-ulp absolute delta and
its fraction of the target.

```text
+------+----------------+----------------+----------------+----------------+----------------+
| node | base drift     | k1 inflation   | k16 inflation  | one-ulp delta  | / target       |
+------+----------------+----------------+----------------+----------------+----------------+
|    0 | 0.000000e+00   | 1.843622e-02   | 2.949795e-01   | 8.742269e-11   | 1.397638e-06   |
|    1 | 0.000000e+00   | 1.516473e-02   | 2.426357e-01   | 6.735312e-11   | 1.076783e-06   |
|    2 | 0.000000e+00   | 1.515867e-01   | 2.425388e+00   | 1.332898e-09   | 2.130921e-05   |
|    3 | 0.000000e+00   | 1.477940e-01   | 2.364704e+00   | 1.191802e-09   | 1.905349e-05   |
|    4 | 0.000000e+00   | 2.173629e-02   | 3.477806e-01   | 1.124067e-10   | 1.797060e-06   |
|    5 | 0.000000e+00   | 1.007490e-01   | 1.611985e+00   | 6.408376e-10   | 1.024515e-05   |
|    6 | 0.000000e+00   | 1.038486e-01   | 1.661577e+00   | 7.050696e-10   | 1.127204e-05   |
|    7 | 0.000000e+00   | 1.085184e-01   | 1.736295e+00   | 8.216871e-10   | 1.313642e-05   |
|    8 | 0.000000e+00   | 7.613999e-02   | 1.218240e+00   | 4.287361e-10   | 6.854258e-06   |
|    9 | 0.000000e+00   | 6.052822e-02   | 9.684516e-01   | 3.254078e-10   | 5.202336e-06   |
|   10 | 0.000000e+00   | 5.230882e-02   | 8.369411e-01   | 2.656320e-10   | 4.246692e-06   |
|   11 | 0.000000e+00   | 4.490932e-02   | 7.185491e-01   | 2.259253e-10   | 3.611896e-06   |
|   12 | 0.000000e+00   | 3.778068e-02   | 6.044909e-01   | 1.851269e-10   | 2.959647e-06   |
|   13 | 0.000000e+00   | 3.117639e-02   | 4.988223e-01   | 1.485192e-10   | 2.374396e-06   |
|   14 | 0.000000e+00   | 1.846551e-02   | 2.954482e-01   | 8.413258e-11   | 1.345038e-06   |
|   15 | 0.000000e+00   | 1.863924e-02   | 2.982278e-01   | 8.497211e-11   | 1.358460e-06   |
|   16 | 0.000000e+00   | 2.528719e-02   | 4.045950e-01   | 1.182102e-10   | 1.889842e-06   |
|   17 | 0.000000e+00   | 3.841914e-02   | 6.147062e-01   | 1.877157e-10   | 3.001034e-06   |
|   18 | 0.000000e+00   | 4.310310e-02   | 6.896496e-01   | 2.141220e-10   | 3.423196e-06   |
|   19 | 0.000000e+00   | 5.106998e-02   | 8.171196e-01   | 2.619355e-10   | 4.187596e-06   |
|   20 | 0.000000e+00   | 5.856897e-02   | 9.371036e-01   | 3.139839e-10   | 5.019701e-06   |
|   21 | 0.000000e+00   | 6.509998e-02   | 1.041600e+00   | 3.574468e-10   | 5.714547e-06   |
|   22 | 0.000000e+00   | 6.812192e-02   | 1.089951e+00   | 3.797042e-10   | 6.070379e-06   |
|   23 | 0.000000e+00   | 7.712909e-02   | 1.234065e+00   | 4.439026e-10   | 7.096727e-06   |
|   24 | 0.000000e+00   | 8.267245e-02   | 1.322759e+00   | 4.734114e-10   | 7.568488e-06   |
|   25 | 0.000000e+00   | 8.893073e-02   | 1.422892e+00   | 5.104156e-10   | 8.160079e-06   |
|   26 | 0.000000e+00   | 9.005440e-02   | 1.440870e+00   | 5.482364e-10   | 8.764725e-06   |
|   27 | 0.000000e+00   | 9.728464e-02   | 1.556554e+00   | 6.028168e-10   | 9.637308e-06   |
|   28 | 0.000000e+00   | 1.003445e-01   | 1.605512e+00   | 6.244270e-10   | 9.982794e-06   |
|   29 | 0.000000e+00   | 1.015049e-01   | 1.624079e+00   | 6.573286e-10   | 1.050880e-05   |
+------+----------------+----------------+----------------+----------------+----------------+
```

Node 2 charge totals: base `8.792971355816406e-09` (identical to the
committed 2229 `exp_lipschitz_charge` of node 2 and to its q-interval
reading), k1 `1.012586911411996e-08`, k16 `3.011933548867331e-08`.

## Controls

```text
gate 2233 reproduction      per-node totals/inflations/max_delta equal to the
                            committed two-node artifact, entry for entry
base drift control          0.0 (bitwise) at all 30 nodes against the
                            committed 2229 exp_lipschitz_charge
level monotonicity          k16 > k1 > base at all 30 nodes; both inflations
                            positive everywhere (no sign anomaly)
```

The k1 pattern tracks the derivative bound `d1 = 2K|x|/a^2 (1-u^2)^-2 + |z|`
against the per-node charge mass: nodes 2 and 3, whose x sits near the
support edge in the family that dominates their charge, carry `~15%` per
ulp; the mid-family nodes sit at `2..10%`.

## What this closes and what it does not

Closed: the 2233 x-channel model charge now has an all-node ledger with a
bitwise re-run control; the binding node's one-ulp cost is `2.13e-05` of
the target at the worst node of the full set.

Not closed:

- the GL/Simpson grids are still the stored binary64 values; k ulps is a
  stated model of the generation error, not a certified enclosure of it
  (the same status as 2233);
- convention A (stored operands exact) remains the certificate reference;
- complete-owner transfer and the signed producer margin remain open;
- no producer or RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_xwidth_charge_all_nodes_2239.py`
  (aggregates the 2233 chunk files; charge backend unchanged)
- inputs: `results/2233x_node*_fam*.json` (900 files),
  `results/2229_q_mpfr_node*.json` (committed charges),
  `results/2233_xwidth_charge.json` (reproduction gate)
- output: `results/2239_xwidth_charge_all_nodes.json`