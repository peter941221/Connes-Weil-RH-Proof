/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGeneratorTranslationSeries

/-!
# Parameterized complete finite Euler product

The synchronized product, its reverse-ordered inverse, and its product-rule
derivative are constructed on the actual common-log carrier.  The right
logarithmic derivative is therefore an output of the same product owner.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedEulerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator

/-- One parameterized Euler factor `I-alpha A_p`. -/
noncomputable def parameterizedPrimeEulerFactor
    (alpha : ℝ) (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  1 - parameterizedPrimeEulerContraction alpha p

/-- Ordered complete finite Euler product. -/
noncomputable def parameterizedFiniteEulerFactor :
    ℝ → List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | _, [] => 1
  | alpha, p :: S =>
      parameterizedPrimeEulerFactor alpha p *
        parameterizedFiniteEulerFactor alpha S

/-- Reverse-ordered inverse of the complete finite Euler product. -/
noncomputable def parameterizedFiniteEulerInverse :
    ℝ → List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | _, [] => 1
  | alpha, p :: S =>
      parameterizedFiniteEulerInverse alpha S *
        parameterizedPrimeEulerInverse alpha p

/-- Product-rule derivative of the synchronized finite Euler product. -/
noncomputable def parameterizedFiniteEulerDerivative :
    ℝ → List CCM24VisiblePrime → finiteSCarrier →L[ℂ] finiteSCarrier
  | _, [] => 0
  | alpha, p :: S =>
      -ccm24PrimeEulerContraction p *
          parameterizedFiniteEulerFactor alpha S +
        parameterizedPrimeEulerFactor alpha p *
          parameterizedFiniteEulerDerivative alpha S

/-- Same-object right logarithmic derivative of the complete product. -/
noncomputable def parameterizedFiniteEulerRightGenerator
    (alpha : ℝ) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  parameterizedFiniteEulerDerivative alpha S *
    parameterizedFiniteEulerInverse alpha S

theorem parameterizedFiniteEulerInverse_mul_factor
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerInverse alpha S *
        parameterizedFiniteEulerFactor alpha S = 1 := by
  induction S with
  | nil =>
      simp [parameterizedFiniteEulerInverse,
        parameterizedFiniteEulerFactor]
  | cons p S ih =>
      rw [parameterizedFiniteEulerInverse,
        parameterizedFiniteEulerFactor]
      calc
        (parameterizedFiniteEulerInverse alpha S *
              parameterizedPrimeEulerInverse alpha p) *
            (parameterizedPrimeEulerFactor alpha p *
              parameterizedFiniteEulerFactor alpha S) =
            parameterizedFiniteEulerInverse alpha S *
              (parameterizedPrimeEulerInverse alpha p *
                parameterizedPrimeEulerFactor alpha p) *
              parameterizedFiniteEulerFactor alpha S := by
          noncomm_ring
        _ = parameterizedFiniteEulerInverse alpha S *
              parameterizedFiniteEulerFactor alpha S := by
          rw [show parameterizedPrimeEulerInverse alpha p *
              parameterizedPrimeEulerFactor alpha p = 1 by
            exact parameterizedPrimeEulerInverse_mul_factor
              alpha p halpha]
          noncomm_ring
        _ = 1 := ih

theorem parameterizedFiniteEulerFactor_mul_inverse
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerFactor alpha S *
        parameterizedFiniteEulerInverse alpha S = 1 := by
  induction S with
  | nil =>
      simp [parameterizedFiniteEulerInverse,
        parameterizedFiniteEulerFactor]
  | cons p S ih =>
      rw [parameterizedFiniteEulerInverse,
        parameterizedFiniteEulerFactor]
      calc
        (parameterizedPrimeEulerFactor alpha p *
              parameterizedFiniteEulerFactor alpha S) *
            (parameterizedFiniteEulerInverse alpha S *
              parameterizedPrimeEulerInverse alpha p) =
            parameterizedPrimeEulerFactor alpha p *
              (parameterizedFiniteEulerFactor alpha S *
                parameterizedFiniteEulerInverse alpha S) *
              parameterizedPrimeEulerInverse alpha p := by
          noncomm_ring
        _ = parameterizedPrimeEulerFactor alpha p *
              parameterizedPrimeEulerInverse alpha p := by
          rw [ih]
          noncomm_ring
        _ = 1 := by
          exact parameterizedPrimeEulerFactor_mul_inverse
            alpha p halpha

/-- The right generator times its own product recovers the product-rule
derivative exactly. -/
theorem parameterizedFiniteEulerRightGenerator_mul_factor
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerRightGenerator alpha S *
        parameterizedFiniteEulerFactor alpha S =
      parameterizedFiniteEulerDerivative alpha S := by
  unfold parameterizedFiniteEulerRightGenerator
  rw [mul_assoc,
    parameterizedFiniteEulerInverse_mul_factor alpha S halpha, mul_one]

/-- For one visible prime, the same-object product generator is the earlier
resolvent generator. -/
theorem parameterizedFiniteEulerRightGenerator_singleton
    (alpha : ℝ) (p : CCM24VisiblePrime) :
    parameterizedFiniteEulerRightGenerator alpha [p] =
      parameterizedPrimeEulerGenerator alpha p := by
  simp only [parameterizedFiniteEulerRightGenerator,
    parameterizedFiniteEulerDerivative, parameterizedFiniteEulerInverse,
    parameterizedFiniteEulerFactor, mul_one, mul_zero, add_zero, one_mul]
  rfl

/-- At `alpha=1`, one parameterized factor is the existing CCM24 factor. -/
theorem parameterizedPrimeEulerFactor_one
    (p : CCM24VisiblePrime) :
    parameterizedPrimeEulerFactor 1 p =
      (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  change u - (((1 : ℝ) : ℂ) • ccm24PrimeEulerContraction p) u =
    ccm24PrimeEulerTransportEquiv p u
  rw [ccm24PrimeEulerTransportEquiv_apply]
  congr 1
  rw [ContinuousLinearMap.smul_apply]
  have hone : (((1 : ℝ) : ℂ)) = 1 := by norm_num
  rw [hone, one_smul, ccm24PrimeEulerContraction,
    ContinuousLinearMap.smul_apply]
  rfl

/-- The synchronized endpoint is exactly the repository's existing CCM24
finite Euler transport, on the same carrier and with the same list order. -/
theorem parameterizedFiniteEulerFactor_one
    (S : List CCM24VisiblePrime) :
    parameterizedFiniteEulerFactor 1 S =
      (ccm24FiniteEulerTransportEquiv S).toContinuousLinearMap := by
  induction S with
  | nil =>
      rw [parameterizedFiniteEulerFactor,
        ccm24FiniteEulerTransportEquiv_nil]
      apply ContinuousLinearMap.ext
      intro u
      rfl
  | cons p S ih =>
      apply ContinuousLinearMap.ext
      intro u
      rw [parameterizedFiniteEulerFactor,
        ContinuousLinearMap.mul_apply,
        parameterizedPrimeEulerFactor_one, ih]
      exact ccm24FiniteEulerTransportEquiv_cons_apply p S u

end CCM24FiniteSParameterizedEulerProduct
end CCM25Concrete
end Source
end ConnesWeilRH
