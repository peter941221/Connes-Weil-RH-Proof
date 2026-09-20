# Record 1783 — GammaR logarithmic derivative readback on the critical line

Date: 2026-09-21

## Result

`ConnesWeilRH/Dev/C1G8R3ScatteringPhaseDigamma.lean` defines the concrete
critical GammaR logarithmic derivative and proves
`ccm24CriticalGammaRLogDeriv_eq_digamma`. At frequency `xi`, the GammaR
argument is exactly `1/2 - 2*pi*i*xi`, and the digamma argument after the
GammaR half-scale is exactly `1/4 - pi*i*xi`.

This is the precise analytic bridge needed to use the landed quarter-half-plane
digamma derivative bound in the scattering-phase calculation. It is formal
interface evidence only: no phase second derivative, W2,1 product, sign, or RH
claim is made here.

Acceptance log: `/home/peter/rh/build-logs/scattering-digamma-v7.log`.
The owning module and paired Audit completed successfully with no `error:`
lines and only `[propext, Classical.choice, Quot.sound]` for the audited
declaration.

Classification: formal project contribution; no originality or RH claim.
