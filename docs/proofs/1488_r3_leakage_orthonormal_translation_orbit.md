# 1488 — R3 normalized orthonormal translation orbit

Date: 2026-09-16.

**Consumer:** the detector-specific healthy-`CompactLog` B5 chain, for the
same selected owner and finite visible-prime family.

**Evidence:** formal Lean result in
[`C1G8R3LeakageOrthonormalOrbit.lean`](../../ConnesWeilRH/Dev/C1G8R3LeakageOrthonormalOrbit.lean),
with paired audit in
[`C1G8R3LeakageOrthonormalOrbitAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3LeakageOrthonormalOrbitAudit.lean).
Acceptance is included in `0916_leakage_three_batches_final.log`.

For the selected compact source test, Lean chooses a natural translation step
strictly greater than twice its support radius. Distinct translates therefore
have disjoint supports. Translation is an isometry on the ambient global L2
carrier, so the normalized right translates form an orthonormal sequence in
`finiteSCarrier`, provided the source test detects a nonzero Laplace value.
That hypothesis also proves the source test has positive L2 norm, so the
normalization is defined.

The sequence is an ambient-carrier orthonormal orbit. This record does not
identify it with the named Hilbert basis of `sourceSoninCarrier` used by the
actual source-compressed G8 diagonal channels. It therefore gives no G8
diagonal trace estimate or readback by itself.
