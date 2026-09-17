# 1594 — Approximate Hardy-tail consumer reaches the G8 boundary ledger

## Verdict

Formal B4 consumer brick.  The G8 visible boundary energy now follows from
the existing radial-leg square sum and, for each factorization owner, an
explicit Hardy-tail square sum.  The exact Hardy-wide support identity is no
longer required for the gap leg.  No estimate for the actual visible-prime
outputs is asserted.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3ApproximateHardyBoundaryConsumer.lean`
- `ConnesWeilRH/Dev/C1G8R3ApproximateHardyBoundaryConsumerAudit.lean`
- Build log: `/home/peter/rh/build-logs/1594_approximate_hardy_boundary.log`
- Acceptance: `Build completed successfully (4072 jobs)`; zero `error:` lines;
  zero `sorryAx`; one standard axiom print.

## Boundary

The remaining B4 producer obligation is now precisely the per-output
Hardy-tail square summability, together with the already separate radial
support/IN-leg premises.  This consumer algebra does not prove those
analytic estimates and does not close S3.
