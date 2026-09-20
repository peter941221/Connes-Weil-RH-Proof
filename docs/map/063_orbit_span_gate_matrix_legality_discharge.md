# 063 — Orbit-span gate matrix legality discharge

Status: formal interface reduced to support data; sign producer open
(2026-09-21).

The generic archimedean-integrability theorem now discharges all pairwise
legality premises in the finite-span gate socket. Thus
`orbitWindowSemiLocalGate (spanObj w y)` is equivalent to the nonpositive
`gateMatrix` quadratic form under only the basis window-support hypothesis.

Evidence: theorem
`C1P2SpanProfileMatrix.orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support`,
Audit output, and
`shortest_route_20260921_span_socket_v5.log`. This is not a sign result.

The shortest live target remains the actual selected OrbitG8 owner: either a
genuine finite-section/span representation with a proved signed matrix
certificate, or a direct same-owner semi-local estimate. The universal
negative-semidefinite matrix route remains ruled out by the existing healthy
detector no-go.
