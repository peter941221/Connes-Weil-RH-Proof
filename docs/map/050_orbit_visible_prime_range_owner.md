# 050 - Orbit visible-prime range owner

Date: 2026-09-20.

Authority: supporting formal interface under the binding route in 003 and
the endpoint boundary in 004.  It does not change route selection.

Record 1742 adds
`visiblePrimeSet_subset_range_of_orbitG8Geometry` to the raw `OrbitG8Geometry`
owner.  The selected convolution square's visible prime-power set is now
available both as the existing support-derived real cutoff and as an explicit
`Finset.range` cutoff indexed by the same orbit owner.

This closes only the finite-domain representation step.  It does not provide
the aggregate sign, the semi-local gate, S3, or RH.  The next consumer is the
same-detector finite prime sum in the B5 sign branch.

Evidence: formal Lean theorem and paired audit in record 1742; accepted log
`build-logs/shortest_route_20260920_g8r0.log`; standard axioms only.
