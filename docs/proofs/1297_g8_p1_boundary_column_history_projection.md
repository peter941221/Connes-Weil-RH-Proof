# 1297 - G8 P1 boundary-column/history projection

The import-facing leaf `C1G8P1BoundaryEnergyExtension` proves the exact
projection estimate

```text
‖finiteEulerMetricBoundaryColumn λ S x‖
  ≤ ‖finiteEulerMetricCoframeHistoryColumn λ S x‖.
```

This is a same-owner carrier statement: the left side is the concrete
`PiLp 2` boundary column and the right side is the completed survivor/boundary
history.  It follows from the `WithLp` second-coordinate contraction after
the existing history apply equation.  No metric-to-radial adapter, finite
prime-power trace identity, sign theorem, remainder limit, or `qw` readback is
introduced.

Status: **formal P1 projection consumer; P2/P3 remain open**.

Evidence: `1393_g8_boundary_energy_extension.log` (green, zero `error:` and
zero `sorryAx`) and the paired audit target.  The same leaf was then extended
with generic basis-level summability and `tsum` domination, and specialized
to the genuine source-prolate Hilbert--Schmidt factor; the owning/audit build
is `1399_g8_boundary_column_prolate.log` (green, zero `error:`/`sorryAx`).
