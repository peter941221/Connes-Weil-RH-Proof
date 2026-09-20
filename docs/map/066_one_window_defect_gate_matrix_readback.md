# 066 — One-window defect gate matrix readback

Status: formal exact readback; signed defect budget open (2026-09-21).

For a one-window defect, the active same-owner gate is exactly the two-span
matrix quadratic form on `[1, -lam]`, with only common support required. This
connects the existing Stage-B defect estimates and the finite matrix owner at
the precise cross-term location.

Evidence: [1758](../proofs/1758_one_window_defect_gate_matrix_readback.md) and
`shortest_route_20260921_defect_matrix_v11.log`.

The remaining producer is an independent signed estimate for this matrix on
the actual OrbitG8 owner. A reference negative gate without cross-term control
is insufficient and is not treated as a proof.
