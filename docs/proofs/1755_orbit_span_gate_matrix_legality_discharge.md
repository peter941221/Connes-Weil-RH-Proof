# 1755 — Orbit span gate matrix legality discharge

Date: 2026-09-21

Record 1754 left pairwise archimedean integrability as an explicit premise of
the finite-span gate socket. The existing generic theorem
`C1ArchimedeanIntegrabilityGeneric.pairTest_legality` proves that premise for
every pair of `CompactLogTest`s. The new theorem
`C1P2SpanProfileMatrix.orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos_of_support`
therefore reduces the same-owner gate/matrix equivalence to the sole window
support hypothesis.

This closes an interface obligation only. It does not construct a finite span
for the selected OrbitG8 owner and does not prove the required matrix sign.
The remaining mathematical target is still the detector-specific signed
semi-local certificate.

Verification: `shortest_route_20260921_span_socket_v5.log`, 3784 jobs, zero
`error:` lines, zero `sorryAx`; the paired Audit prints only
`[propext, Classical.choice, Quot.sound]`.
