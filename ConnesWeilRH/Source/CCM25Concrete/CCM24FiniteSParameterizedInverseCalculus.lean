/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerCalculus

/-!
# Calculus of the finite Euler inverse

On the legal synchronized interval, the reverse Neumann product is
differentiated through canonical Banach-algebra inversion.  This avoids any
termwise differentiation of the multi-prime renewal.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSParameterizedInverseCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerCalculus
open NormedRing ContinuousLinearMap Ring

/-- Exact inverse derivative `-T⁻¹ T' T⁻¹`. -/
noncomputable def parameterizedFiniteEulerInverseDerivative
    (alpha : ℝ) (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  -(parameterizedFiniteEulerInverse alpha S *
      parameterizedFiniteEulerDerivative alpha S *
      parameterizedFiniteEulerInverse alpha S)

/-- The reverse Neumann product has the canonical inverse derivative within
the full legal synchronized interval. -/
theorem hasDerivWithinAt_parameterizedFiniteEulerInverse
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivWithinAt
      (fun beta : ℝ => parameterizedFiniteEulerInverse beta S)
      (parameterizedFiniteEulerInverseDerivative alpha S)
      (Set.Icc (-1 : ℝ) 1) alpha := by
  let R := finiteSCarrier →L[ℂ] finiteSCarrier
  let unit := parameterizedFiniteEulerUnit alpha S halpha
  have hcanonical :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) unit).comp_hasDerivAt alpha
      (hasDerivAt_parameterizedFiniteEulerFactor alpha S)
  have hcanonical' : HasDerivAt
      (fun beta : ℝ => Ring.inverse
        (parameterizedFiniteEulerFactor beta S))
      (parameterizedFiniteEulerInverseDerivative alpha S) alpha := by
    simpa only [Function.comp_apply,
      parameterizedFiniteEulerUnit_inv_val,
      ContinuousLinearMap.neg_apply, mulLeftRight_apply,
      parameterizedFiniteEulerInverseDerivative] using hcanonical
  have halpha_mem : alpha ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨(abs_le.mp halpha).1, (abs_le.mp halpha).2⟩
  apply hcanonical'.hasDerivWithinAt.congr_of_mem _ halpha_mem
  intro beta hbeta
  symm
  exact ringInverse_parameterizedFiniteEulerFactor beta S
    (abs_le.mpr hbeta)

/-- Interior synchronized times have the same ordinary norm derivative. -/
theorem hasDerivAt_parameterizedFiniteEulerInverse
    (alpha : ℝ) (S : List CCM24VisiblePrime) (halpha : |alpha| < 1) :
    HasDerivAt
      (fun beta : ℝ => parameterizedFiniteEulerInverse beta S)
      (parameterizedFiniteEulerInverseDerivative alpha S) alpha := by
  apply (hasDerivWithinAt_parameterizedFiniteEulerInverse alpha S
    halpha.le).hasDerivAt
  exact Icc_mem_nhds (abs_lt.mp halpha).1 (abs_lt.mp halpha).2

end CCM24FiniteSParameterizedInverseCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
