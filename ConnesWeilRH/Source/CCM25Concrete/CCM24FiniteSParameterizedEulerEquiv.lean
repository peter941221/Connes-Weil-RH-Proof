/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerCommutation

/-!
# Parameterized finite Euler equivalence

The synchronized Euler product and its reverse Neumann product are packaged
as a genuine bounded equivalence for every `|alpha| <= 1`.  This is the
ambient transport used by the moving Sonin geometry.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedEulerEquiv

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerGenerator
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerCommutation

/-- Algebraic equivalence underlying the synchronized finite Euler
transport. -/
noncomputable def parameterizedFiniteEulerLinearEquiv
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier ≃ₗ[ℂ] finiteSCarrier where
  toFun := parameterizedFiniteEulerFactor alpha S
  invFun := parameterizedFiniteEulerInverse alpha S
  left_inv u := by
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u)
      (parameterizedFiniteEulerInverse_mul_factor alpha S halpha)
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
      using h
  right_inv u := by
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T u)
      (parameterizedFiniteEulerFactor_mul_inverse alpha S halpha)
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
      using h
  map_add' u v := (parameterizedFiniteEulerFactor alpha S).map_add u v
  map_smul' c u := (parameterizedFiniteEulerFactor alpha S).map_smul c u

/-- The actual bounded invertible synchronized transport. -/
noncomputable def parameterizedFiniteEulerEquiv
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier ≃L[ℂ] finiteSCarrier :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    (parameterizedFiniteEulerLinearEquiv alpha S halpha)
    ‖parameterizedFiniteEulerFactor alpha S‖
    ‖parameterizedFiniteEulerInverse alpha S‖
    (parameterizedFiniteEulerFactor alpha S).le_opNorm
    (parameterizedFiniteEulerInverse alpha S).le_opNorm

@[simp]
theorem parameterizedFiniteEulerEquiv_apply
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    parameterizedFiniteEulerEquiv alpha S halpha u =
      parameterizedFiniteEulerFactor alpha S u :=
  rfl

@[simp]
theorem parameterizedFiniteEulerEquiv_symm_apply
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (u : finiteSCarrier) :
    (parameterizedFiniteEulerEquiv alpha S halpha).symm u =
      parameterizedFiniteEulerInverse alpha S u :=
  rfl

/-- Its continuous linear map is definitionally the same synchronized
product used to construct the right generator. -/
theorem parameterizedFiniteEulerEquiv_toContinuousLinearMap
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (parameterizedFiniteEulerEquiv alpha S halpha).toContinuousLinearMap =
      parameterizedFiniteEulerFactor alpha S := by
  rfl

/-- The inverse map is the reverse-ordered Neumann product. -/
theorem parameterizedFiniteEulerEquiv_symm_toContinuousLinearMap
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (parameterizedFiniteEulerEquiv alpha S halpha).symm.toContinuousLinearMap =
      parameterizedFiniteEulerInverse alpha S := by
  rfl

/-- At synchronized time one, the moving equivalence is the pre-existing
CCM24 finite Euler transport. -/
theorem parameterizedFiniteEulerEquiv_one
    (S : List CCM24VisiblePrime) :
    parameterizedFiniteEulerEquiv 1 S (by norm_num) =
      ccm24FiniteEulerTransportEquiv S := by
  apply ContinuousLinearEquiv.ext
  funext u
  change parameterizedFiniteEulerFactor 1 S u =
    ccm24FiniteEulerTransportEquiv S u
  rw [parameterizedFiniteEulerFactor_one]
  rfl

/-- The right generator attached to this exact equivalence is the complete
additive prime-power generator. -/
theorem parameterizedFiniteEulerEquiv_rightGenerator_eq
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedFiniteEulerDerivative alpha S *
        (parameterizedFiniteEulerEquiv alpha S halpha).symm.toContinuousLinearMap =
      parameterizedFiniteEulerGenerator alpha S := by
  rw [parameterizedFiniteEulerEquiv_symm_toContinuousLinearMap]
  exact parameterizedFiniteEulerRightGenerator_eq_additiveGenerator
    alpha S halpha

end CCM24FiniteSParameterizedEulerEquiv
end CCM25Concrete
end Source
end ConnesWeilRH
