# 065 — One-window defect two-span bridge

Status: formal structural bridge; defect budget remains open (2026-09-21).

`C1P2SpanProfileMatrix.oneWindowICdefect_eq_twoSpan` identifies every
one-window Stage-B defect exactly with a two-element genuine `CompactLogTest`
span. This lets any future defect estimate and its matrix certificate use the
same finite gate owner.

Evidence: [1757](../proofs/1757_one_window_defect_two_span_bridge.md) and
`shortest_route_20260921_defect_span_v10.log`.

The route is not closed: the selected OrbitG8 owner still needs an independent
same-owner defect budget (or direct semi-local sign estimate). The reference
negative-gate certificate alone is insufficient.
