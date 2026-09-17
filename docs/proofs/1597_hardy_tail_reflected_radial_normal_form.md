# 1597 — Hardy tail is exactly a reflected radial leakage

## Verdict

Formal B4 normalization brick. For every source column `A`, the involution law
for the Hardy--Titchmarsh operator gives

`A - H E_w H A = H (I - E_w) H A`.

Thus the approximate B4 tail is not an unspecified error: it is the radial
complement of the Hardy-transformed column, transported by the same involution
that already relates the selected root to its reflected owner.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumer.lean`
- `ConnesWeilRH/Dev/C1G8R3ApproximateHardySupportConsumerAudit.lean`
- Build log: `/home/peter/rh/build-logs/1597_hardy_radial_tail_identity_retry6.log`
- Acceptance: `Build completed successfully (4071 jobs)`; zero `error:` lines;
  zero `sorryAx`; two standard axiom prints.

## Boundary

The identity does not prove square summability. The remaining B4 producer is a
radial-complement estimate for the Hardy-transformed actual Schur columns,
with the root-gap operator and source-side factors attached.
