# 1026 - Lane R mass-relative tail bridge

Date: 2026-08-18.

## Verdict

The Gamma_R tail owner now has a parameterized interface for a profile
constant supplied by a later analytic certificate.  For a convolution square,
the resulting budget can be written in terms of the square mass
`(g.convolutionSquare.test 0).re`.

This closes an interface, not the missing estimate.  The mass-relative local
profile bound and the finite `N = 21` constrained-prefix inequality remain
open.  No universal constant `C` is asserted.

## Lean Owner

`Dev/C1XiCenterTwoGammaTailEstimate.lean` adds
`gammaRArchProfileTailNorm_le_explicit_rate_of_pointwise_majorant`.  It
consumes explicit head and support-tail bounds and returns the existing rate

```text
L / (2*N)
  + 2 * ||F.test 0|| * exp(-(2*N+1)*(supportRadius(F)+1))
      / (1-exp(-2*(supportRadius(F)+1))).
```

`Dev/C1XiCenterTwoGammaMassRelativeTail.lean` proves
`convolutionSquare_zero_norm_eq_re`, then specializes the parameter to
`L = C * (g.convolutionSquare.test 0).re`.  Its main output is
`gammaRArchProfileTailNorm_le_mass_scaled_rate`, whose head premise is

```text
||profile_n(g^* * g, y)||
  <= C * (g^* * g)(0) * y * exp(-2*n*y)
```

on `0 < y <= supportRadius(g^* * g) + 1`.  The support-side exponential
bound is inherited from the general compact-support owner.

The same module assembles this budget through
`archimedeanTerm_nonpos_of_mass_scaled_prefix_bound` and its strict companion.
Those consumers still require the finite-prefix inequality as an explicit
premise.

## Remaining Gap

The existing Cauchy-Schwarz theorem
`C1LaneRNarrowArch.convolutionSquare_norm_le_mass` controls the profile value,
but it does not control the derivative/Lipschitz constant used to obtain the
`n^-2` origin bound.  Therefore it is invalid to infer the mass-scaled head
premise from that theorem alone.  A future producer must either:

1. prove a derivative or modulus estimate for the selected finite-dimensional
   owner; or
2. replace the absolute tail budget with a coupled quadratic-form estimate.

## Verification

WSL2 ext4 owner and probe verification completed at `3541` jobs.  The new
declarations report only:

```text
[propext, Classical.choice, Quot.sound]
```

The result does not prove a finite-prefix sign, global spectral
nonnegativity, unconditional RH, or a prime-inclusive Lane R theorem.
