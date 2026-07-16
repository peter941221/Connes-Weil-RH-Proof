/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedSoninKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov

/-!
# Parameterized finite-S Euler generator

This module constructs the genuine common-log bounded operator
`X_p(alpha) = -A_p (I-alpha A_p)⁻¹`, where
`A_p=p⁻¹/² U_(-log p)`.  Its geometric modes are actual one-sided
prime-power translations, not abstract finite-matrix channels.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedEulerGenerator

open scoped BigOperators
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkov

/-- The scaled Euler contraction `alpha A_p`. -/
noncomputable def parameterizedPrimeEulerContraction
    (alpha : ℝ) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (alpha : ℂ) • ccm24PrimeEulerContraction p

theorem norm_parameterizedPrimeEulerContraction_lt_one
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    ‖parameterizedPrimeEulerContraction alpha p‖ < 1 := by
  rw [parameterizedPrimeEulerContraction, norm_smul, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    |alpha| * ‖ccm24PrimeEulerContraction p‖ ≤
        1 * ‖ccm24PrimeEulerContraction p‖ :=
      mul_le_mul_of_nonneg_right halpha (norm_nonneg _)
    _ < 1 := by
      simpa using norm_ccm24PrimeEulerContraction_lt_one p

/-- The exact Neumann inverse `(I-alpha A_p)⁻¹`. -/
noncomputable def parameterizedPrimeEulerInverse
    (alpha : ℝ) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ∑' n : ℕ, parameterizedPrimeEulerContraction alpha p ^ n

theorem parameterizedPrimeEulerInverse_mul_factor
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedPrimeEulerInverse alpha p *
        (1 - parameterizedPrimeEulerContraction alpha p) = 1 := by
  exact geom_series_mul_neg (parameterizedPrimeEulerContraction alpha p)
    (norm_parameterizedPrimeEulerContraction_lt_one alpha p halpha)

theorem parameterizedPrimeEulerFactor_mul_inverse
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (1 - parameterizedPrimeEulerContraction alpha p) *
        parameterizedPrimeEulerInverse alpha p = 1 := by
  exact mul_neg_geom_series (parameterizedPrimeEulerContraction alpha p)
    (norm_parameterizedPrimeEulerContraction_lt_one alpha p halpha)

/-- The genuine right logarithmic derivative
`T_p'(alpha) T_p(alpha)⁻¹`. -/
noncomputable def parameterizedPrimeEulerGenerator
    (alpha : ℝ) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  -ccm24PrimeEulerContraction p *
    parameterizedPrimeEulerInverse alpha p

/-- Resolvent identity characterizing the right logarithmic derivative. -/
theorem parameterizedPrimeEulerGenerator_mul_factor
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedPrimeEulerGenerator alpha p *
        (1 - parameterizedPrimeEulerContraction alpha p) =
      -ccm24PrimeEulerContraction p := by
  unfold parameterizedPrimeEulerGenerator
  rw [mul_assoc,
    parameterizedPrimeEulerInverse_mul_factor alpha p halpha, mul_one]

/-- The `n`th prime-power mode, corresponding to `m=n+1`. -/
noncomputable def parameterizedPrimeEulerGeneratorMode
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  -ccm24PrimeEulerContraction p *
    (parameterizedPrimeEulerContraction alpha p ^ n)

/-- The actual generator is the operator-norm sum of its translation modes. -/
theorem parameterizedPrimeEulerGenerator_eq_tsum_modes
    (alpha : ℝ) (p : CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedPrimeEulerGenerator alpha p =
      ∑' n : ℕ, parameterizedPrimeEulerGeneratorMode alpha p n := by
  have hsummable : Summable
      (fun n : ℕ => parameterizedPrimeEulerContraction alpha p ^ n) :=
    summable_geometric_of_norm_lt_one
      (norm_parameterizedPrimeEulerContraction_lt_one alpha p halpha)
  unfold parameterizedPrimeEulerGenerator parameterizedPrimeEulerInverse
  rw [← hsummable.tsum_mul_left (-ccm24PrimeEulerContraction p)]
  rfl

/-- Each mode is the literal translation by `-(n+1) log p`, with the exact
critical Euler coefficient and synchronized-time power. -/
theorem parameterizedPrimeEulerGeneratorMode_apply
    (alpha : ℝ) (p : CCM24VisiblePrime) (n : ℕ) (u : finiteSCarrier) :
    parameterizedPrimeEulerGeneratorMode alpha p n u =
      (-((alpha : ℂ) ^ n) *
          (ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) •
        cc20GlobalLogTranslation
          (-((n + 1 : ℕ) : ℝ) * Real.log p) u := by
  unfold parameterizedPrimeEulerGeneratorMode
    parameterizedPrimeEulerContraction
  rw [smul_pow]
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, map_smul]
  rw [← ContinuousLinearMap.mul_apply, ← pow_succ',
    primeEulerContraction_pow_apply p (n + 1) u]
  simp only [smul_neg, smul_smul, neg_smul, neg_mul]

/-- Complete synchronized generator for an ordered finite visible-prime
family.  The sum is taken before any norm or absolute value. -/
noncomputable def parameterizedFiniteEulerGenerator
    (alpha : ℝ) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (S.map (parameterizedPrimeEulerGenerator alpha)).sum

@[simp]
theorem parameterizedFiniteEulerGenerator_nil (alpha : ℝ) :
    parameterizedFiniteEulerGenerator alpha [] = 0 := by
  rfl

theorem parameterizedFiniteEulerGenerator_cons
    (alpha : ℝ) (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    parameterizedFiniteEulerGenerator alpha (p :: S) =
      parameterizedPrimeEulerGenerator alpha p +
        parameterizedFiniteEulerGenerator alpha S := by
  rfl

end CCM24FiniteSParameterizedEulerGenerator
end CCM25Concrete
end Source
end ConnesWeilRH
