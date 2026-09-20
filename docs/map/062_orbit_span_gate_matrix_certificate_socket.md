# 062 — Orbit-span gate matrix certificate socket

Status: formal interface landed; producer sign remains open (2026-09-21).

The active healthy-`CompactLog` B5 route now has the exact theorem
`C1P2SpanProfileMatrix.orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos`.
For a finite real span, the same-owner orbit-window gate is equivalent to the
nonpositive finite gate-matrix quadratic form, assuming only window support and
pairwise archimedean integrability. This is a formal reduction, not a sign
certificate and not an RH result.

Evidence: `docs/proofs/1754_orbit_span_gate_matrix_certificate_socket.md` and
build log `shortest_route_20260921_span_gate_v4.log`; the paired Audit prints
the standard three axioms and no `sorryAx`.

The shortest live producer attack is now the concrete owner step: identify or
construct a finite span for the selected OrbitG8 detector, then prove the
corresponding `-gateMatrix` positive-semidefinite bound. If that owner cannot
be represented in the finite span, the fallback is an explicit finite-section
approximation with a separately proved readback error; no normalized B5 or
universal B1 route is opened.
