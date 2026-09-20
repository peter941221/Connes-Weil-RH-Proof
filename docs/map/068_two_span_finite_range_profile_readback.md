# 068 — Two-span finite-range profile readback

Status: formal finite-domain readback; signed aggregate estimate remains open
(2026-09-21).

For two compact-log basis tests `A`, `B` supported in `(-R,R)`, the exact
`p2AggregateValue` of the same span owner `[A,B]` with coefficients
`[1,-lam]` is now rewritten as its Archimedean term plus the explicit finite
range `range (ceil(exp(2R)) + 1)` of the convolution square. This consumes the
existing support-to-range theorem without changing the owner.

Evidence: theorem
`twoSpan_p2Aggregate_eq_archimedean_plus_rangeProfile` in
`C1P2SpanProfileMatrix.lean`, paired Audit, and
`shortest_route_20260921_range_readback_v14.log`.

This is a formal representation result, not a sign estimate. The active
healthy-`CompactLog`, detector-specific B5 route still needs the signed
finite-range aggregate inequality for the actual OrbitG8 owner.
