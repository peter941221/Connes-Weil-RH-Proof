# 1955 — Parametric Mean Gap Domination for the Degree-Four Orbit Polynomial

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1ParametricMeanGapDomination` formalizes the exact algebraic
expansion, difference factorization, and universal parametric domination of the
bipartite mean gap for the degree-four orbit polynomial:

$$P_{\delta, \gamma}(\omega) = (\delta^2 + \gamma^2 - \omega^2)^2 + 4 \delta^2 \omega^2$$

Key theorems formalized:

1. `orbitPoly_eq_expansion`:
   Proves the exact biquadratic expansion:
   $$P_{\delta, \gamma}(\omega) = (\delta^2 + \gamma^2)^2 - 2(\gamma^2 - \delta^2)\omega^2 + \omega^4$$

2. `orbitPoly_sub`:
   Proves the exact difference identity:
   $$P_{\delta, \gamma}(\omega_1) - P_{\delta, \gamma}(\omega_2) = (\omega_2^2 - \omega_1^2)[2(\gamma^2 - \delta^2) - (\omega_1^2 + \omega_2^2)]$$

3. `orbitPoly_sub_pos`:
   Proves that for any frequencies $\omega_1^2 < \omega_2^2$ and zero height satisfying
   $\omega_1^2 + \omega_2^2 < 2(\gamma^2 - \delta^2)$, the between-group gap is strictly positive.

4. `parametric_mean_gap_sufficient_condition`:
   Proves that when the lower bound on the mean gap $\Delta P \ge \text{gap\_bound} > 0$
   dominates the internal variance $(C_1 - C_2)(C_1 \text{var}_1) < C_1 C_2 (\text{gap\_bound})^2$,
   the ANOVA mean gap condition is unconditionally satisfied.

5. `exists_pos_lambda_quadratic_neg_of_parametric_domination`:
   Transfers the parametric domination condition to the existence of an explicit strictly
   positive span coefficient $\lambda > 0$ with strictly negative span gate quadratic.

6. `orbitPoly_gap_at_omega_zero_and_four`:
   Proves that for any non-trivial zero satisfying $\gamma^2 - \delta^2 \ge 190$
   (which holds for all critical strip zeros since $|\gamma| > 14$ and $|\delta| < 1/2$),
   the frequency shift between $\omega_1 = 0$ and $\omega_2 = 4$ satisfies:
   $$P_{\delta, \gamma}(0) - P_{\delta, \gamma}(4) \ge 16 \times (380 - 16) = 5700$$

## Verification

```text
Build completed successfully (3812 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```
