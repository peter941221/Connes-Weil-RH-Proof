# 2364 - Symmetric coordinate charge

日期：2026-10-02。

The owner coordinate bridge now handles mixed displacement orientation. The
new theorem `correctedPhysical_weighted_coordinate_transfer2359` splits on
`actual ≤ ideal` versus `ideal ≤ actual`, uses the appropriate endpoint
estimate, and returns one bound with `|ideal - actual|`. The only geometric
assumption is that the interval between the two coordinates lies inside the
owner window.

This matches the 2359 diagnostic, where the stored `np.linspace` coordinates
do not all lie on one side of the exact affine coordinates. The theorem is
still an analytic bridge: the full 240001 coordinate-pair facts, the numeric
displacement maximum, directed accumulation, and trapezoid remainder have
not been imported into Lean.

Status: `SYMMETRIC_OWNER_ANALYTIC_BRIDGE_ONLY`; producer GO: `false`.
