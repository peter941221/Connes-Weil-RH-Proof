# 3243: cell 16923 rectangular aggregate

Status: Lean-verified enclosure interface; no negative sign claim.

Record 3243 preserves real and imaginary coordinates as ComplexRect2427
intervals. It multiplies the exact coefficient point, the cell-specific bump
rectangle, and the 512-fold phase rectangle for each owner family, then sums
the 30 family rectangles.

Lean proves bump, phase, family, and aggregate rectangle membership. The
theorem record2680_cell16923_unweighted_rect_value_upper3243 exports the exact
unweighted physical real-part upper as the aggregate rectangle reHi.

The direct all-family norm_num sign expansion exceeded the practical heartbeat
budget and is not a certificate. The next step is a smaller sign-aware block
decomposition with local reHi thresholds.

Verification used WSL2 ext4, the project Lean toolchain v4.30.0, and the audit
module C1RouteAConcreteOwnerCell16923UnweightedSign3243Audit. All five audited
theorems use exactly propext, Classical.choice, and Quot.sound.
