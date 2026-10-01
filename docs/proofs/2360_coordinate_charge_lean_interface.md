# 2360 - Coordinate-charge interface

日期：2026-10-01。

The full-grid replay in record 2359 uses stored `np.linspace` coordinates,
while `stripNorm_le_nodeUpper2348` requires nodes of the exact affine form
`-radius + index * step`. Record 2360 isolates that mismatch in
`C1RouteACoordinateCharge.lean`.

`nodeUpper_of_coordinate_charge2359` proves the purely ordered composition:
an actual-grid upper, an analytic transfer charge, and a final charged upper
give the exact-grid upper. Its Lipschitz specialization additionally takes a
nonnegative Lipschitz constant and an explicit coordinate displacement bound.
This makes the missing 2341 coordinate charge a named hypothesis rather than
an implicit equality assumption.

The audit module was checked with the available WSL Lean command, but the
normal Lake build remains subject to the pre-existing locally modified
`.lake/packages/mathlib` checkout documented in 2355. No numerical replay,
coordinate identity, directed accumulation theorem, producer import, or RH
claim is made here; the node theorem still requires supplied analytic and
numeric hypotheses.

Status: `INTERFACE_ONLY`; producer GO: `false`.
