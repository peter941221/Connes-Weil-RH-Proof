# Record 1784 — Critical-line digamma endpoint and GammaR symbol derivative

Date: 2026-09-21

## Result

The actual CCM24 GammaR half-scale has real part exactly `1/4`, while the
existing series derivative theorem was stated on the strict half-plane
`Re z > 1/4`. The new theorem
`hasDerivAt_digamma_criticalQuarterLine` closes this endpoint by using

```text
digamma(z + 1) = digamma(z) + z^(-1)
```

at a point with positive real part. The strict theorem is used at `z + 1`,
and the inverse correction is differentiated explicitly. This yields the
critical-line derivative as `digamma'(z + 1) + z^(-2)`.

The theorem
`hasDerivAt_ccm24CriticalGammaRLogDeriv` then differentiates the exact
GammaR-to-digamma readback along the real frequency variable, producing the
factor `-i*pi/2` times `digamma'` at the quarter-line argument.

Acceptance log: `/home/peter/rh/build-logs/scattering-digamma-v14.log`.
The owning module and paired Audit completed successfully in 3554 jobs;
the audited declarations use only `[propext, Classical.choice, Quot.sound]`
and no `sorryAx`.

## Boundary

This is formal analytic progress toward the scattering phase's second
derivative. It does not yet prove the phase-product W2,1 estimate, detector
semi-local positivity, a sign theorem, or RH.

Classification: formal project contribution; no originality or RH claim.
