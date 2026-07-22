# Proof 498: Schur--Markov absolute uniform bound

Date: 2026-07-22

## Result

The result is a genuine family-uniform estimate for the complete corrected
signed cocycle, but it does not close Gate 3U.  The distinction is the final
Schur--Markov scalar.

Write

```text
rho_S =finiteEulerLowerFactor(S)/finiteEulerUpperFactor(S),
C_S   =rho_S * raw actual-band remainder.
```

Lean proves, without any analytic producer premise,

```text
norm(Tr(C_S))
  <=(18+6 H_lambda)(c-a)^2 seminorm_0,0(g)^2,
```

where

```text
H_lambda
 =sum_i norm(sourceProlateHilbertSchmidtFactor(lambda)(e_i))^2.
```

The right side is independent of the finite visible-prime family.  The
complete outer, reflected-outer, second-support, and prolate owner is assembled
before the trace norm is taken, and no primewise absolute value occurs.

## Mixed normalization

The new input is the exact factorization

```text
rho_S * finiteEulerMetricCoframe_S

 =[(finiteEulerUpperFactor(S))^-1 * transport_S^dagger]
    *[finiteEulerLowerFactor(S) * dualFrame_S].
```

Both bracketed maps are contractions.  The first follows from the exact upper
transport bound, and the second is the existing normalized restricted-inverse
bound.  Therefore

```text
norm(rho_S * finiteEulerMetricCoframe_S)<=1.
```

This controls `rho_S` times the complete raw endpoint through the existing
four-branch physical trace owner.  Combining it with the already uniform
actual first-jet bound gives the displayed `18+6 H_lambda` estimate for the
corrected cocycle.

## Exact boundary

The same module proves the equivalence

```text
norm(Tr(C_S))<=rho_S * P

  iff

norm(Tr(raw actual-band remainder_S))<=P.
```

Since `rho_S>0`, the extra relative factor cannot be obtained from the new
absolute estimate by renaming its constant.  It is exactly the unresolved raw
quadratic-remainder estimate.  Likewise, Proof 497's numerator-only target is
equivalent to the stronger raw endpoint estimate and is not a substitute for
the corrected first-jet-minus-endpoint owner.

## Lean ownership

The source and audit are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSSchurMarkovUniformBound.lean

ConnesWeilRH/Dev/
  CCM24FiniteSSchurMarkovUniformBoundAudit.lean
```

The central declarations are

```text
schurMarkovMixedMetricCoframe_eq_normalized_factors
norm_schurMarkovMixedMetricCoframe_le_one
schurMarkovScaledSourceBandGramTrace_norm_le_supportEnergy
suffixEulerLowerFactorCompletedSignedCocycle_trace_norm_le_supportEnergy
suffixEulerCompletedSignedCocycle_relative_bound_iff_raw_bound.
```

## Boundary

Proof 498 closes an absolute `S`-uniform bound, not the relative
`rho_S`-scaled bound.  Gate 3U, the finite-S sign, negative-owner integration,
Burnol's identity, and RH remain open.  The next valid target is still the
same-object raw quadratic-remainder trace bound with compact root support kept
before every absolute value.
