# Record 2501 — corrected owner exponent split inputs

Record 2499 used the maximum endpoint ratio in a cell.  That is the wrong
direction for an upper bound on
`exp(-30/(1-a^2))`: the exponent is decreasing in `a`, so the cell bound must
use the minimum `|x/r|`.  The corrected generator uses zero for cells crossing
zero and the nearer endpoint for same-sign cells.

The corrected exact artifact is `results/2501_owner_exp_split_inputs.json`.
It is input data only.  The per-cell Lean inequality, hcell closure, producer
margin, and RH remain open.  Record 2499 is historical and superseded for
this input direction.
