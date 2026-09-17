# 1593 — Gap-free endpoint bound lifts to a countable spectral ledger

## Verdict

Formal S3 interface brick. The finite endpoint-moment inequality now has a
countable `tsum` form. It assumes summability of the zeroth moment, the first
defect, and the explicit endpoint-mass sequence, then passes the pointwise
inequality through the summation filter and rewrites the scalar multiple and
sum.

This is gap-free and contains no numerical or spectral-gap premise.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3GapFreeEndpointMoment.lean`
- `ConnesWeilRH/Dev/C1G8R3GapFreeEndpointMomentAudit.lean`
- Build log: `/home/peter/rh/build-logs/1593_gap_free_endpoint_tsum_retry7.log`
- Acceptance: `Build completed successfully (8476 jobs)`; zero `error:` lines;
  zero `sorryAx`; two standard axiom prints.

## Boundary

The theorem still needs to be instantiated with the actual endpoint spectral
measure of the Sonin-carrier operator. Proving its zeroth/first moment and
endpoint-mass summability remains the analytic S3 obligation.
