# 1949 — Bipartite signed variance-gap gate certificate

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1SignedVarianceIdentity` proves the general bipartite
partition decomposition of the finite signed-variance determinant, establishing
the variance-gap negativity criterion and connecting it directly to the
four-point span vertex gate certificate:

1. `bipartite_double_sum_split`:
   for any disjoint partition `s₁ ∪ s₂` and symmetric bivariate function `F`,
   the double sum over `(s₁ ∪ s₂)²` splits into the internal double sums on
   `s₁²` and `s₂²` plus twice the cross sum on `s₁ × s₂`.

2. `finite_signed_variance_bipartite_identity`:
   the signed variance determinant decomposes exactly into the internal
   variances on `s₁` and `s₂` minus the positive-negative cross gap energy:
   ```text
   (∑ c_i p_i^2) (∑ c_i) - (∑ c_i p_i)^2
     = (1/2) ∑_{s₁²} c_i c_j (p_i - p_j)^2
       + (1/2) ∑_{s₂²} c_i c_j (p_i - p_j)^2
       - ∑_{s₁ × s₂} c_i (-c_j) (p_i - p_j)^2
   ```

3. `finite_signed_variance_bipartite_neg`:
   whenever the cross gap energy strictly dominates the internal positive
   variances:
   ```text
   (1/2) ∑_{s₁²} c_i c_j (p_i - p_j)^2 + (1/2) ∑_{s₂²} c_i c_j (p_i - p_j)^2
     < ∑_{s₁ × s₂} c_i (-c_j) (p_i - p_j)^2,
   ```
   the variance determinant is strictly negative.

4. `exists_pos_lambda_quadratic_neg_of_bipartite_variance_gap`:
   combines positive total weight, positive cross sum, and the bipartite
   variance-gap domination condition to produce a strictly positive span
   coefficient with a strictly negative span gate quadratic:
   ```text
   (∑ c_i p_i^2) - lam * (2 * ∑ c_i p_i) + lam^2 * (∑ c_i) < 0.
   ```

## Route impact

This formalizes the multi-node variance-gap reduction of Map 103 (records
1919/1920) beyond the simple two-atom case. It directly interfaces with
`C1FourPointSpanGateCertificate.exists_pos_lambda_quadratic_neg_of_det_neg`,
reducing the span gate negativity obligation to proving that the cross-gap
energy between the positive-mass zone (Archimedean / positive primes) and the
negative-mass zone (negative prime oscillation) dominates the internal
variances.

## Verification

```text
20260924_bipartite_variance_identity.log: Build completed successfully (3811 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```

The proof is exact finite algebra, summation reindexing, and ring arithmetic.
No numerical approximations or floating-point shortcuts are used.
