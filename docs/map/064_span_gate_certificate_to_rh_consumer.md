# 064 — Span gate certificate to RH consumer

Status: final consumer formalized; producer certificate open (2026-09-21).

`C1P2SpanProfileMatrix.sourceRH_of_right_orbitGeometry_spanGateCertificate`
now gives the shortest exact end-to-end consumer for a finite-span attack:
same-owner OrbitG8 geometry + finite span representation + support + matrix
quadratic-form nonpositivity implies `SourceRH`.

Evidence: proof record [1756](../proofs/1756_span_gate_certificate_to_rh_consumer.md)
and `shortest_route_20260921_span_consumer_v7.log`; the paired Audit has only
the standard three axioms and no `sorryAx`.

This does not close RH. The unresolved producer is unchanged and explicit:
construct the actual selected OrbitG8 owner in a useful finite section/span and
prove its detector-specific signed matrix certificate. A global
negative-semidefinite matrix theorem is not permitted by the existing healthy
detector no-go.
