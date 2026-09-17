# 1597 — Hardy tail is exactly a reflected radial leakage

## Verdict

Formal B4 normalization brick. The Hardy involution gives, for every source
column A and every wide radial projection E_w,

`A - H E_w H A = H (I - E_w) H A`.

Thus the approximate B4 tail is a transported radial complement, rather than
an unspecified error term. It has the operator shape needed for comparison
with the reflected-root radial chain.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumer.lean`
- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumerAudit.lean`
- Build log: `/home/peter/rh/build-logs/1597_hardy_radial_tail_identity_retry6.log`
- Acceptance: `Build completed successfully (4071 jobs)`; zero `error:` lines;
  zero `sorryAx`; two standard axiom prints.

## Boundary

The identity supplies no square-summability. The remaining B4 producer is a
radial-complement estimate for the Hardy-transformed actual Schur columns,
with the root-gap operator and source-side factors attached.
