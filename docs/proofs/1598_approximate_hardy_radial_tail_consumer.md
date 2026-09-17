# 1598 — Approximate B4 consumer in reflected-radial form

## Verdict

Formal B4 interface brick. The approximate Hardy-tail consumer now accepts
the exact operator `H (I - E_w) H A` directly. The boundary-energy consumer
uses this form, so the remaining B4 producer is stated without the expanded
subtraction ambiguity.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumer.lean`
- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumerAudit.lean`
- `ConnesWeilRH/Dev/C1G8R3ApproximateHardyBoundaryConsumer.lean`
- Build log: `/home/peter/rh/build-logs/1598_approximate_hardy_radial_tail_retry.log`
- Acceptance: `Build completed successfully (4072 jobs)`; zero `error:` lines;
  zero `sorryAx`; one standard axiom print.

## Boundary

No B4 estimate is proved. The open obligation is still square-summability of
the reflected radial-complement columns for the actual Schur boundary
operators. S3 remains the source-compressed leakage square-sum.
