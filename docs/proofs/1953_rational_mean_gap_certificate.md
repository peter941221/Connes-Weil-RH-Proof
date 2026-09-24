# 1953 — Rational Mean Gap Gate Certificates

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1BipartiteMeanGapCertificate` formalizes rational moment
certificates for the bipartite mean gap gate inequality, providing exact unconditional
theorems:

1. `BipartiteMeanGapCertificate`:
   packages $(C₁, C₂, \bar{p}₁, \bar{p}₂, \text{var}₁, \text{var}₂)$ with proofs of:
   - $hC : 0 < C₁ - C₂$
   - $hB : 0 < 2 * (C₁ \bar{p}₁ - C₂ \bar{p}₂)$
   - $hgap : 0 < C₁ C₂ (\bar{p}₁ - \bar{p}₂)^2 + (C₁ - C₂)(C₂ \text{var}₂ - C₁ \text{var}₁)$

2. `exists_pos_lambda_quadratic_neg_of_cert`:
   unconditionally deduces the existence of a strictly positive coefficient
   $\lambda > 0$ with strictly negative gate quadratic:
   ```text
   (C₁ * (var₁ + p₁_bar^2) - C₂ * (var₂ + p₂_bar^2)) -
     lam * (2 * (C₁ * p₁_bar - C₂ * p₂_bar)) +
     lam^2 * (C₁ - C₂) < 0.
   ```

3. Four concrete certified instances corresponding to the certified detector family:
   - `cert_c10_g14` ($c = 1.0, \gamma = 14.13$)
   - `cert_c13_g14` ($c = 1.3, \gamma = 14.13$)
   - `cert_c10_g21` ($c = 1.0, \gamma = 21.02$)
   - `cert_c13_g21` ($c = 1.3, \gamma = 21.02$)
   All certificate conditions are certified by `by norm_num`.

4. Four unconditional theorems completely discharging all gate preconditions:
   - `exists_pos_lambda_quadratic_neg_c10_g14`
   - `exists_pos_lambda_quadratic_neg_c13_g14`
   - `exists_pos_lambda_quadratic_neg_c10_g21`
   - `exists_pos_lambda_quadratic_neg_c13_g21`

## Verification

```text
Build completed successfully (3811 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```
