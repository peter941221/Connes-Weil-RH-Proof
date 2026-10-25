# 3097 - Coarse transition-jet enclosure does not clear the target

Status: routing diagnostic; the tested coarse certificates are insufficient.
This is not a lower bound on the actual derivative integrals.

The decision question is whether the D4/D7 interval proof can be shortened by
using the existing recurrence on 256, 512, 1024 or 2048 uniform cells. The
same rational-exponential transition jet as record 3070 is evaluated on
`[1/128,1/2]`. Even this subinterval's D4 upper enclosure exceeds the full
target 1500 for every tested cell count. Adding a nonnegative endpoint
allowance cannot make that particular upper certificate clear the target.

The result rejects only those coarse uniform partitions with this evaluator.
A loose upper bound does not prove that the actual D4 integral exceeds 1500.
The 8192-cell formal comparison in record 3067 remains open; finer or adaptive
partitions and analytically tighter interval formulas are not excluded.

Reproduce with `python3 scripts/coarse_seed_enclosure_probe_3097.py`.
The artifact `results/3097_coarse_seed_enclosure_probe.json` retains exact
rational upper endpoints, decimal diagnostics, partition controls and 24
independent midpoint derivative-reference checks. These controls validate the
routing experiment, not a Lean rounding or integral certificate.

No exported floating-point reading is used by records 3095 or 3096.
