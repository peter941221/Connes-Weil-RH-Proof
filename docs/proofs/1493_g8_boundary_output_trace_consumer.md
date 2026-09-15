# 1493 — Per-output boundary energies feed the actual G8 trace consumer

Date: 2026-09-16.

**Consumer:** convergence of the literal four-channel G8 physical metric
trace for the same selected detector and healthy `CompactLog` owner.

**Evidence:** formal Lean declaration
[`tendsto_ordinaryTraceAlong_g8PhysicalMetricCutoff_of_each_boundary_output_summable`](../../ConnesWeilRH/Dev/C1G8R3BoundaryOutputTraceConsumer.lean)
with paired audit
[`C1G8R3BoundaryOutputTraceConsumerAudit.lean`](../../ConnesWeilRH/Dev/C1G8R3BoundaryOutputTraceConsumerAudit.lean).
Acceptance log: `0916_g8_boundary_trace_consumer_try2.log`; build completed
successfully (3965 jobs), zero `error:` lines, zero `sorryAx`, and one
standard-axiom audit terminator.

The corollary replaces the aggregate boundary-energy premise by
square-summability of every actual finite-prime boundary output after the
same selected root convolution. It invokes the existing exact finite-sum
reduction from record 1492 and then the actual four-channel trace-limit
theorem. The survivor diagonal energy premise and the existing mixed
survivor/boundary trace limit remain as before.

The per-output energy assumptions have not been proved. This closes neither
the unconditional trace limit nor the signed endpoint readback, detector-
specific `qw` positivity, C3, or RH.
