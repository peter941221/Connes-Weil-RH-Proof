# 1952 — Bipartite ANOVA Mean Gap Identity & Gate Negativity

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1SignedVarianceIdentity` proves the exact bipartite ANOVA
mean gap decomposition and gate negativity certificates:

1. `bipartite_variance_mean_gap_identity`:
   for any positive and negative cluster masses $C_1, C_2$, cluster means
   $\bar{p}_1, \bar{p}_2$, and variances $\text{var}_1, \text{var}_2$, the gate
   determinant decomposes as:
   ```text
   (C₁ * p₁_bar - C₂ * p₂_bar)^2 -
     (C₁ - C₂) * (C₁ * (var₁ + p₁_bar^2) - C₂ * (var₂ + p₂_bar^2)) =
   C₁ * C₂ * (p₁_bar - p₂_bar)^2 + (C₁ - C₂) * (C₂ * var₂ - C₁ * var₁).
   ```
   Divided by $(C_1 - C_2)^2$, this reproduces the exact signed-variance identity
   of Record 1919:
   $$\text{Var}_\nu(P) = (1+f) \text{Var}_1 - f \text{Var}_2 - f(1+f) \Delta^2.$$

2. `exists_pos_lambda_quadratic_neg_of_mean_gap_condition`:
   whenever $C_1 - C_2 > 0$, the linear cross term is positive, and the mean gap
   plus variance surplus condition holds:
   ```text
   0 < C₁ * C₂ * (p₁_bar - p₂_bar)^2 + (C₁ - C₂) * (C₂ * var₂ - C₁ * var₁),
   ```
   there exists an explicit strictly positive coefficient $\lambda$ with
   strictly negative span gate quadratic:
   ```text
   D - lam * (2 * B₀₁) + lam^2 * C < 0.
   ```

3. `exists_pos_lambda_quadratic_neg_of_sufficient_mean_gap`:
   sufficient condition where positive mean gap dominates positive cluster variance:
   ```text
   (C₁ - C₂) * (C₁ * var₁) < C₁ * C₂ * (p₁_bar - p₂_bar)^2.
   ```

4. `exists_pos_lambda_gate_and_prefix_of_mean_gap_condition`:
   master 103 Cut-2 bridge wiring the mean gap condition directly to the healthy
   detector owner, supplying a strictly positive coefficient carrying both the
   nonpositive span gate and the negative spectral prefix bound:
   ```text
   orbitWindowSemiLocalGate (h(lam)) ∧ Re(∑ spectralTerm) ≤ -xiMultiplicity(rho) * lam^2.
   ```

## Numerical Evidence (Record 1951 / 1952)

Tested across the 12 certified cases anchored at $c \in [1.0, 1.3]$:
- Cross domination ratio $E_{\text{cross}} / (V_1 + V_2) \in [1.49, 4.13] > 1$ (100% pass);
- Net mass $C_1 - C_2 \approx 0.41 \sim 0.71 > 0$;
- Determinant $\text{det} \in [-3.30 \times 10^6, -7.02 \times 10^5] < 0$;
- Both the mean gap $-C_1 C_2 \Delta^2 < 0$ and the variance difference
  $(C_1 - C_2)(C_1 \text{var}_1 - C_2 \text{var}_2) < 0$ contribute negatively.
