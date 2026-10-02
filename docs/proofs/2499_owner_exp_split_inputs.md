# Record 2499 — exact owner/cell exponent split inputs

The 2498 split envelope is now connected to the actual owner geometry at the
input level.  `scripts/routea_owner_exp_split_inputs_2499.py` reconstructs the
stored rational owner radii and the 640-cell strip grid, then computes for
every safe family/cell pair

`z = 30 / (1 - a^2) = n + r`, with `n = floor(z)` and `0 <= r < 1`.

The resulting JSON contains exact integer/rational payloads, not binary64
approximations.  It has 9,994 local pairs and 9,206 baseline pairs; the
largest local integer part is `n = 12,682`.  Baseline pairs are explicitly
marked because the Lean hybrid definition selects the L1 branch outside a
family's support-safe cell.

This closes only the decomposition-input layer.  The remaining obligation is
to consume the payloads in the weighted-curvature expression, prove the
Taylor/power bound for each branch, and compare the resulting rational upper
sum against a repriced table.  No hcell proof, producer GO, or RH claim is
made.
