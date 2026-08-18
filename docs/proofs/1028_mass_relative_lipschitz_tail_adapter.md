# 1028 - Mass-relative Lipschitz tail adapter

Date: 2026-08-19.

## Verdict

The Gamma_R tail route now has a concrete adapter from a support-local
Lipschitz certificate to the existing square-mass tail budget.  The adapter is
conditional: it consumes the certificate and does not prove a universal
mass-relative Lipschitz constant.

The logical shape is:

```text
support-local Lipschitz certificate with coefficient C_L * mass
                              |
                              v
paired profile head coefficient (2 * C_L + 1) * mass
                              |
                              v
existing shifted-tail rate gammaRArchProfileTailMassRate g (2*C_L+1) N
```

This is an interface closure for a future finite-band, derivative-energy, or
coupled quadratic producer.  The Lane R inequality, global spectral
nonnegativity, and RH remain open.

## Lean owners

`Dev/C1XiCenterTwoGamma.lean` exposes
`gammaRArchProfileTerm_norm_le_of_support_lipschitz`.  With an explicit
nonnegative `Lip`, it proves, for `0 < y <= supportRadius F + 1`,

```text
||gammaRArchProfileTerm F n y||
  <= (2 * Lip + ||F.test 0||) * y * exp(-2*n*y).
```

The nonnegativity field is part of the API because the final multiplication
monotonicity step needs the coefficient to be nonnegative; it is not left to
an implicit tactic assumption.

`Dev/C1XiCenterTwoGammaMassRelativeTail.lean` adds
`gammaRArchProfileTerm_norm_le_mass_scaled_of_support_lipschitz`.  Its input
is the explicit certificate

```text
||F.test x - F.test z||
  <= (C_L * (F.test 0).re) * ||x - z||
```

on the support interval for `F = g.convolutionSquare`, together with
`0 <= C_L`.  The convolution-square zero identity rewrites
`||F.test 0||` to the nonnegative real mass, so the head coefficient becomes
`(2 * C_L + 1) * mass`.

The direct tail consumer
`gammaRArchProfileTailNorm_le_mass_scaled_rate_of_support_lipschitz` then
returns

```text
(2*C_L + 1) * mass / (2*N)
  + 2 * mass * exp(-(2*N+1)*(supportRadius(F)+1))
      / (1-exp(-2*(supportRadius(F)+1))).
```

The finite-prefix inequality is still a separate premise of the existing
prefix/tail sign consumers.  No prefix sign is inferred here.

## Verification

WSL2 ext4 verification used the shared Lean lock:

```text
lake build ConnesWeilRH.Dev.C1XiCenterTwoGamma
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaProbe
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaMassRelativeTail
lake build ConnesWeilRH.Dev.C1XiCenterTwoGammaMassRelativeTailProbe
```

The owner completed at 3541 jobs and the mass-relative probe at 3542 jobs.
The probe audits the new declarations to:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project axiom, RH root axiom, or numerical-to-Lean
transfer in this adapter.

## Boundary

The 1027 numerical stress screen found that an interior derivative lower bound
for normalized D3 roots grows from about `72.7` to `256.5` as frequency rises
from `0` to `256`.  That evidence rejects assuming a small frequency-uniform
`C_L`; it does not rule out a finite-band or owner-specific certificate.

The next substantive producer is therefore a derivative-energy certificate or
a coupled quadratic tail estimate.  This document records the adapter only,
not that missing producer.
