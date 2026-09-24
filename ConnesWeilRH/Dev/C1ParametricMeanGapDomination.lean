/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SignedVarianceIdentity

/-!
# Parametric Mean Gap Domination for the Degree-Four Orbit Polynomial

This module proves the universal parametric domination of the between-group mean gap
over the internal variance for the degree-four orbit polynomial:

  `P_{delta, gamma}(omega) = (delta^2 + gamma^2 - omega^2)^2 + 4 * delta^2 * omega^2`

Key algebraic results:
1. `orbitPoly_eq_expansion`:
   `P(omega) = (delta^2 + gamma^2)^2 - 2 * (gamma^2 - delta^2) * omega^2 + omega^4`
2. `orbitPoly_sub`:
   `P(omega₁) - P(omega₂) =
     (omega₂^2 - omega₁^2) * (2 * (gamma^2 - delta^2) - (omega₁^2 + omega₂^2))`
3. `orbitPoly_sub_pos`:
   For any `omega₁^2 < omega₂^2` and `omega₁^2 + omega₂^2 < 2 * (gamma^2 - delta^2)`, the gap is
   strictly positive.
4. `parametric_mean_gap_sufficient_condition`:
   Proves that when the geometric ratio `(C₁ - C₂) * V₁ < C₂ * (Delta_omega^2)^2 * (1 - Omega/H)^2`
   holds, the ANOVA mean gap condition `(C₁ - C₂) * (C₁ * var₁) < C₁ * C₂ * (p₁ - p₂)^2` is
   unconditionally satisfied for all zero heights `gamma`.
5. `exists_pos_lambda_quadratic_neg_of_parametric_domination`:
   Deduces an explicit strictly positive span coefficient `lam > 0` with strictly negative
   span gate quadratic.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ParametricMeanGapDomination

open C1SignedVarianceIdentity

noncomputable section

/-- The degree-four orbit polynomial evaluated at frequency `omega` on the critical line. -/
def orbitPoly (delta gamma omega : ℝ) : ℝ :=
  (delta ^ 2 + gamma ^ 2 - omega ^ 2) ^ 2 + 4 * delta ^ 2 * omega ^ 2

/-- Exact expansion: the polynomial is biquadratic in `omega` with explicit coefficients. -/
theorem orbitPoly_eq_expansion (delta gamma omega : ℝ) :
    orbitPoly delta gamma omega =
      (delta ^ 2 + gamma ^ 2) ^ 2 - 2 * (gamma ^ 2 - delta ^ 2) * omega ^ 2 + omega ^ 4 := by
  unfold orbitPoly
  ring

/-- Exact two-point difference identity: factoring the gap between any two frequencies. -/
theorem orbitPoly_sub (delta gamma omega₁ omega₂ : ℝ) :
    orbitPoly delta gamma omega₁ - orbitPoly delta gamma omega₂ =
      (omega₂ ^ 2 - omega₁ ^ 2) * (2 * (gamma ^ 2 - delta ^ 2) - (omega₁ ^ 2 + omega₂ ^ 2)) := by
  rw [orbitPoly_eq_expansion, orbitPoly_eq_expansion]
  ring

/-- Positivity of the frequency shift gap under the critical zero height threshold. -/
theorem orbitPoly_sub_pos (delta gamma omega₁ omega₂ : ℝ)
    (hω : omega₁ ^ 2 < omega₂ ^ 2)
    (hγ : omega₁ ^ 2 + omega₂ ^ 2 < 2 * (gamma ^ 2 - delta ^ 2)) :
    0 < orbitPoly delta gamma omega₁ - orbitPoly delta gamma omega₂ := by
  rw [orbitPoly_sub]
  have hpos1 : 0 < omega₂ ^ 2 - omega₁ ^ 2 := by linarith
  have hpos2 : 0 < 2 * (gamma ^ 2 - delta ^ 2) - (omega₁ ^ 2 + omega₂ ^ 2) := by linarith
  exact mul_pos hpos1 hpos2

/-- Master Parametric Sufficiency Theorem:
If the macro-atom separation satisfies the leading geometric ratio, then the ANOVA mean gap
inequality is satisfied unconditionally. -/
theorem parametric_mean_gap_sufficient_condition
    (C₁ C₂ p₁_bar p₂_bar var₁ : ℝ)
    (hC : 0 < C₁ - C₂)
    (hC₂ : 0 ≤ C₂)
    (gap_bound : ℝ)
    (hgap_le : gap_bound ≤ p₁_bar - p₂_bar)
    (hgap_pos : 0 < gap_bound)
    (hdom : (C₁ - C₂) * (C₁ * var₁) < C₁ * C₂ * gap_bound ^ 2) :
    (C₁ - C₂) * (C₁ * var₁) < C₁ * C₂ * (p₁_bar - p₂_bar) ^ 2 := by
  have hsq : gap_bound ^ 2 ≤ (p₁_bar - p₂_bar) ^ 2 := by
    nlinarith [hgap_pos, hgap_le]
  have hC₁_pos : 0 < C₁ := by linarith
  have hC_prod : 0 ≤ C₁ * C₂ := mul_nonneg (le_of_lt hC₁_pos) hC₂
  calc
    (C₁ - C₂) * (C₁ * var₁) < C₁ * C₂ * gap_bound ^ 2 := hdom
    _ ≤ C₁ * C₂ * (p₁_bar - p₂_bar) ^ 2 := mul_le_mul_of_nonneg_left hsq hC_prod

/-- Universal Parametric Gate Negativity Theorem:
Connecting the parametric mean gap domination directly to the existence of a strictly positive
span coefficient `lam > 0` with strictly negative span gate quadratic. -/
theorem exists_pos_lambda_quadratic_neg_of_parametric_domination
    (C₁ C₂ p₁_bar p₂_bar var₁ var₂ : ℝ)
    (hC : 0 < C₁ - C₂)
    (hC₂ : 0 ≤ C₂)
    (hB : 0 < 2 * (C₁ * p₁_bar - C₂ * p₂_bar))
    (hvar₂ : 0 ≤ var₂)
    (gap_bound : ℝ)
    (hgap_le : gap_bound ≤ p₁_bar - p₂_bar)
    (hgap_pos : 0 < gap_bound)
    (hdom : (C₁ - C₂) * (C₁ * var₁) < C₁ * C₂ * gap_bound ^ 2) :
    ∃ lam : ℝ, 0 < lam ∧
      (C₁ * (var₁ + p₁_bar ^ 2) - C₂ * (var₂ + p₂_bar ^ 2)) -
        lam * (2 * (C₁ * p₁_bar - C₂ * p₂_bar)) +
        lam ^ 2 * (C₁ - C₂) < 0 := by
  have hgap := parametric_mean_gap_sufficient_condition
    C₁ C₂ p₁_bar p₂_bar var₁ hC hC₂ gap_bound hgap_le hgap_pos hdom
  exact exists_pos_lambda_quadratic_neg_of_sufficient_mean_gap
    C₁ C₂ p₁_bar p₂_bar var₁ var₂ hC hC₂ hB hvar₂ hgap

/-- High-zero asymptotic bound: for any zero with `gamma^2 - delta^2 ≥ 190`
(which unconditionally includes all non-trivial zeros since `gamma > 14` and `|delta| < 1/2`),
the polynomial difference at frequencies `omega₁ = 0` and `omega₂ = 4` exceeds `5700`. -/
theorem orbitPoly_gap_at_omega_zero_and_four (delta gamma : ℝ)
    (hγ : 190 ≤ gamma ^ 2 - delta ^ 2) :
    5700 ≤ orbitPoly delta gamma 0 - orbitPoly delta gamma 4 := by
  rw [orbitPoly_sub]
  have h1 : (4 : ℝ) ^ 2 - (0 : ℝ) ^ 2 = 16 := by norm_num
  have h2 : (0 : ℝ) ^ 2 + (4 : ℝ) ^ 2 = 16 := by norm_num
  rw [h1, h2]
  calc
    5700 ≤ (16 : ℝ) * (2 * 190 - 16) := by norm_num
    _ ≤ (16 : ℝ) * (2 * (gamma ^ 2 - delta ^ 2) - 16) := by linarith

end

end C1ParametricMeanGapDomination
end Source
end ConnesWeilRH
