# 1595 — Endpoint mass is finite under spectral tail decay

## Verdict

Formal S3 producer interface brick. If the endpoint diagonal values tend to
zero along the chosen Hilbert basis, then for every threshold below one the
endpoint indicator is eventually zero, hence summable. This removes the
endpoint-mass term as an independent assumption once actual spectral-tail
decay is supplied.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3GapFreeEndpointMoment.lean`
- `ConnesWeilRH/Dev/C1G8R3GapFreeEndpointMomentAudit.lean`

## Boundary

The actual Sonin operator still needs a theorem identifying its endpoint
diagonal sequence and proving convergence to zero. No such spectral-tail
estimate is asserted here, so S3 remains open.
