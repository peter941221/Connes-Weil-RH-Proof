# 3242: concrete cell 16923 bump and weighted value interface

Status: Lean-verified cell-specific bump and weighted value upper; no negative cell sign claim.

The external 3238 diagnostic identifies cell 16923 as a strongly cancelling cell. All 30 owner families are active there; representative weighted real contributions include approximately -377.6 from family 14 and +269.9 from family 15. Therefore this cell cannot use the single-family endpoint pattern from records 3228 and 3229.

Record 3242 copies the verified order-30 bump enclosure argument from record 3231 to the exact coordinate record2680Center3212 16923. It proves record2680_cell16923_bump_mem3242.

The companion value file constructs exact bump balls, reuses the generic phase and weight balls from 3241, and proves record2680_cell16923_value_upper3242. This is a formal Lean upper bound for the exact weighted original integrand. It does not import the Arb JSON result and does not claim the upper is negative.

A direct norm_num attempt to prove the resulting 30-family taxi-ball upper strictly negative expanded the exact rational expression but left the final center.re plus radius inequality unresolved. This indicates that the current independent taxi-ball propagation is too wide or too syntactically complex for this cancellation cell. The next enclosure must preserve more correlation or split the family aggregate into sign-aware blocks.

Verification used WSL2 ext4 with Lean 4.30.0. The bump module, value module, and audit build successfully with exactly [propext, Classical.choice, Quot.sound].