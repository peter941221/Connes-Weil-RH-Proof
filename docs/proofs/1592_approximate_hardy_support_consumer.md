# 1592 — B4 admits an approximate Hardy-support consumer

## Verdict

Formal interface improvement for B4. Let `H` be the Hardy--Titchmarsh
involution and `E_w` the radial projection at the wider scale. Split an
actual source column `A` as

`A = H E_w H A + (A - H E_w H A)`.

The first summand has `E_w H (H E_w H A) = H (H E_w H A)` by involutivity and
projection idempotence, so the existing composite B4 theorem applies. The
second summand is retained as an explicit Hardy-tail square-sum. A finite
Hilbert-space sum-of-squares argument then gives the full gap-leg estimate.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumer.lean`
- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumerAudit.lean`
- Build log: `/home/peter/rh/build-logs/1592_approximate_hardy_support_retry4.log`
- Acceptance: `Build completed successfully (4071 jobs)`; zero `error:` lines;
  zero `sorryAx`; one standard `Quot.sound` axiom print.

## Boundary

This does not prove the tail square-sum for the actual visible-prime Schur
outputs. It changes the analytic B4 target from exact support to a concrete
Hardy-tail estimate, which is the next producer obligation.
