# 1591 — Gap-free endpoint-moment inequality is machine-checked

## Verdict

Formal, finite-spectral bookkeeping brick for S3. For values `0 ≤ m_i ≤ 1`
and `0 < epsilon ≤ 1`, the finite zeroth moment is bounded by

`(1 + epsilon⁻¹)` times the finite first defect plus the count of values in
`[1 - epsilon, 1]`.

The proof is elementary: below `1 - epsilon`, multiply the deficit estimate
by `epsilon` and divide by the positive epsilon; at the endpoint, charge one
unit to the explicit endpoint counter. It uses no spectral gap and no numeric
input.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3GapFreeEndpointMoment.lean`
- `ConnesWeilRH/Dev/C1G8R3GapFreeEndpointMomentAudit.lean`
- Build log: `/home/peter/rh/build-logs/1591_gap_free_endpoint_moment_retry5.log`
- Acceptance: `Build completed successfully (8476 jobs)`; zero `error:` lines;
  zero `sorryAx`; one standard `Quot.sound` axiom print.

## Boundary

This does not prove S3. The remaining work is to instantiate the moment data
from the actual Sonin-carrier operator and prove the strip-density and
endpoint-mass estimates, including the carrier-existence obligation recorded
in 1590.
