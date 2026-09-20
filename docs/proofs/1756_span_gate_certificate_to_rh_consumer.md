# 1756 — Finite-span gate certificate to RH consumer

Date: 2026-09-21

## Result

The finite-span producer contract is now connected directly to the existing
same-owner exit. The theorem
`C1P2SpanProfileMatrix.sourceRH_of_right_orbitGeometry_spanGateCertificate`
says that, for every right-oriented hypothetical off-line zero, it is enough
to provide one `OrbitG8Geometry` owner together with:

1. an equality of that owner with a finite real `spanObj`;
2. open-window support for every span basis test; and
3. a nonpositive quadratic form for the corresponding `gateMatrix`.

The proof converts the matrix certificate to the same-owner orbit gate, then
uses the exact finite signed-budget bridge and the existing `SourceRH`
consumer. No conclusion is stored as data and no RH premise is introduced.

## Verification

`C1P2SpanProfileMatrix` and its Audit target built successfully in
`shortest_route_20260921_span_consumer_v7.log` (3784 jobs), with zero
`error:` lines and zero `sorryAx`. The focused Audit prints exactly
`[propext, Classical.choice, Quot.sound]` for the new theorem.

## Remaining producer

The theorem is conditional. The actual selected OrbitG8 owner still has to be
represented by such a finite span and supplied with the signed matrix
certificate. The universal negative-semidefinite matrix route remains ruled
out by the healthy-detector no-go; this contract is detector-specific.
