# Proof 645: normalized arbitrary-suffix metric row

## Result

The result is good but does not close Bone 1.  Proof 645 proves that the
condition-number growth of every literal suffix coframe is removed by the
exact Schur--Markov scalar

```text
rho_S
  = suffixEulerSchurMarkovScalar(S)
  = finiteEulerLowerFactor(S) / finiteEulerUpperFactor(S).
```

For every list `S`, not only a list presented as
`FinitePrimePowerFamily.visiblePrimes`, Lean proves

```text
||rho_S MetricCoframe_S|| <= 1,
||rho_S ForwardCoframe_S|| <= 1,
||rho_S EndpointCoframe_S|| <= 2,
||rho_S BoundaryMoment_S|| <= 3 ||detector||.
```

The proof reconstructs the literal-list restricted Euler inverse and factors
the dual frame as

```text
target inclusion * restricted inverse^dagger.
```

The lower-factor-normalized inverse adjoint and the upper-factor-normalized
transport adjoint are both contractions.  Their product is exactly
`rho_S MetricCoframe_S`; no family wrapper, permutation argument, or hidden
condition-number estimate is used.

## Coupled hard row

The old orientation and survivor/boundary residual rows are first recombined
into their genuine adjacent metric-coframe telescope:

```text
Hard_(p,S)
  = MetricOrientation_(p,S) + MetricResidual_(p,S).
```

Only after this equality is established does Lean insert the longer suffix
scalar.  The result is

```text
||rho_(p::S) Hard_(p,S)|| <= 2 ||detector||.
```

The orientation and residual terms are not estimated separately.  The
inclusion/forward row retains its elementary bound after the same scaling:

```text
||rho_(p::S) Known_(p,S)|| <= 6 ||detector||.
```

This `6` is rebuilt from the exported detector-leg, forward-leakage, Schur
transition, and old-frame contraction bounds.  It does not depend on the
commented experimental block in `CoframeOrientationLedger.lean`.

Consequently the complete source objects satisfy

```text
||rho_(p::S) SignedTelescope_(p,S)|| <= 8 ||detector||,
||rho_(p::S) ReducedRow_(p,S)|| <= 8 ||detector||,
||rho_(p::S) Interior_(p,S)|| <= 8 ||detector||.
```

The last step uses only the exact Proof 638 readback

```text
Interior = ReducedRow * normalizedPrimeEulerInverse^dagger * newFrame
```

and the fact that the last two maps are contractions.

## Bone 1 meaning

```text
 arbitrary suffix metric growth
             |
             v
 +------------------------------------+
 | exact rho_(p::S) normalization     |
 | complete numerator norm <= 8 ||D|| |
 +------------------------------------+
             |
             v
 missing: remove rho_(p::S), or prove the
 signed same-vector response contains it
```

This is the first family-uniform bound for the complete arbitrary-suffix
numerator, but it is in the normalized gauge.  Bone 1 is unnormalized and
pointwise relative to

```text
L_p^dagger newFrame_(p,S).
```

Dividing by `rho_(p::S)` is not uniform as the suffix grows.  Route validity
is only `(p :: S).Nodup` and supplies no positive lower bound for this product.
The remaining source theorem must therefore recover the suffix scalar inside
the complete signed response, or bypass the absolute numerator norm with the
direct same-vector antiresonant factorization.

Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorNormalizedSuffixMetricRow.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorNormalizedSuffixMetricRowAudit.lean
```

## Verification

The Ubuntu-24.04 WSL2 ext4 source/audit build passed under the shared Lake
lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| normalized suffix metric source      |  3413 | PASS   |
| focused 23-declaration audit         |  3414 | PASS   |
+--------------------------------------+-------+--------+
```

All twenty-three audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
