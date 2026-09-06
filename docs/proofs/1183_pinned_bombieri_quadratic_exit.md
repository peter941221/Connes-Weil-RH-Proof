# 1183 — Pinned direct-quadratic P2 exit

Date: 2026-09-06

The theorem
`sourceRH_of_pinnedOrbitDetector_p2BombieriQuadraticP2BridgeData` packages the
direct Hermitian P2 socket together with the already-exported orbit support and
visible-prime cutoff.  For each right-oriented off-line zero, one producer
must return the same `g,n` carrying:

- `HealthyYoshidaDetectorData rho.1 g`;
- `support g.test ⊆ (-((n+2):Real),(n+2))`;
- `q < exp (2(n+2))` for every visible prime-power `q`; and
- `Nonempty (BombieriQuadraticP2BridgeData g)`.

The exit consumes only the direct finite positivity to obtain `qw g ≥ 0`, then
uses the existing healthy-detector contradiction.  The support/cutoff fields
are owner-audit data and do not claim a sign.  No RH theorem is asserted.
