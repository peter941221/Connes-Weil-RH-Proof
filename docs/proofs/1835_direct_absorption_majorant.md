# 1835 — Direct absorption majorant and prime weight factoring

Date: 2026-09-22

## Result

`C1P2DirectAbsorptionMajorant.lean` formalizes the exact factoring of the
finite visible-prime majorant into an arithmetic prime weight sum and a
uniform profile supremum bound:

```text
sum_{n in visible} (Lambda(n)/sqrt(n)) * |(bilateralProfile (log n)).re|
  <= (sum_{n in visible} (Lambda(n)/sqrt(n))) * B
  <= (sum_{n in visible} Lambda(n)) * B
```

It establishes:
1. `visiblePrimeWeightSum geometry`: the exact finite arithmetic weight sum
   `sum_{n in range} Lambda(n) / sqrt(n)`, proved nonnegative.
2. `visibleChebyshevPrimeSum geometry`: the unweighted Chebyshev sum
   `sum_{n in range} Lambda(n)`, proved nonnegative and majorizing `visiblePrimeWeightSum`.
3. `isProfileUniformBound geometry B`: uniform bound on the absolute bilateral profile
   over visible prime-power coordinates.
4. `sum_weighted_profile_le_weightSum_mul_bound`: exact algebraic factoring
   `sum (Lambda/sqrt) * |profile| <= visiblePrimeWeightSum * B`.
5. `absorptionWitness_of_uniform_profile_bound`: construction of `OrbitG8AbsorptionWitness`
   from `visiblePrimeWeightSum * B <= - archimedeanTerm`.
6. `riemannHypothesis_of_uniform_profile_bounds`: master theorem deriving Mathlib's
   canonical `RiemannHypothesis` directly from factored uniform profile bounds.
7. `absorptionWitness_of_chebyshev_bound`: construction from Chebyshev majorant.
8. `riemannHypothesis_of_chebyshev_bounds`: master theorem deriving Mathlib's
   canonical `RiemannHypothesis` directly from Chebyshev prime majorants.

The module and its paired audit `C1P2DirectAbsorptionMajorantAudit.lean` build clean,
zero error, zero sorryAx, standard axioms only `[propext, Classical.choice, Quot.sound]`.

## Boundary

This completely decouples the arithmetic prime book from the single-detector
profile bound B. The remaining mathematical task is to bound B on the selected
orbit owner and compare it with the negative Archimedean margin.
