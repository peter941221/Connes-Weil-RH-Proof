# 039 — R3 actual-cutoff diagonal detector-root energy

**Authority:** supporting.

**Status:** formal positive-square and same-basis trace-energy identities for
each diagonal G8 metric channel at every finite cutoff. No diagonal cutoff
limit is established.

**Consumer:** the same-owner G8 trace ledger for the detector-selected
semi-local B5 readback on a healthy `CompactLog` owner and its finite
visible-prime family. The binding route in
[003](003_b1_b5_minimal_exit_route_selection.md) is unchanged.

The paired Lean leaf
[`C1G8R3DiagonalRootLegNormalForm.lean`](../../ConnesWeilRH/Dev/C1G8R3DiagonalRootLegNormalForm.lean)
proves that, for any diagonal coframe `L`, its cutoff channel is `A_n† A_n`,
where `A_n` is the selected detector root after `L` and the actual
source-compressed cutoff. The ordinary trace on the named source basis is
exactly `sum_i ||A_n e_i||^2`. See [proof record
1484](../proofs/1484_r3_actual_cutoff_diagonal_root_energy.md).

The survivor and boundary energy sums are only known finite separately at
each cutoff. Their uniform domination and convergence remain open; records
[018](018_r3_unit_detector_root_square_sum.md),
[022](022_r3_common_right_causal_telescope.md), and
[028](028_r3_moving_scale_detector_root_range_energy.md) identify the
remaining leakage/common-right square-sum work. Record
[1485](../proofs/1485_r3_diagonal_trace_limit_energy_constraint.md) formally
shows that any finite real diagonal trace limit would force square-summability
of the uncut same-owner root columns. It does not provide that estimate or a
trace limit. The total G8 readback, signed remainder decay, `qw` identification
and sign, P2, C3, and RH remain open.
