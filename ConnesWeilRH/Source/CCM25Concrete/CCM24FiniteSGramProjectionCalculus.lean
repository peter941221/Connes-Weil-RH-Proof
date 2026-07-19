/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramInverseCalculus

/-!
# Calculus of the Gram-corrected moving Sonin projection

The actual moving orthogonal projection is represented by the differentiable
frame formula `A (A^dagger A)^-1 A^dagger`.  This module proves its operator
norm derivative before simplifying it to the off-diagonal flow.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGramProjectionCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedSoninProjection
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open _root_.ConnesWeilRH.CC20Concrete

noncomputable local instance sourceSoninCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Canonical differentiable Gram projection path. -/
noncomputable def parameterizedCanonicalGramProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  gramCorrectedProjection
    (parameterizedSoninFrame lambda alpha S)
    (Ring.inverse (parameterizedSoninGram lambda alpha S))

/-- Product-rule derivative of `A G^-1 A^dagger`. -/
noncomputable def parameterizedCanonicalGramProjectionDerivative
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (parameterizedSoninFrameDerivative lambda alpha S ∘L
        parameterizedSoninGramInv lambda alpha S halpha +
      parameterizedSoninFrame lambda alpha S ∘L
        parameterizedSoninGramInverseDerivative lambda alpha S halpha) ∘L
      ContinuousLinearMap.adjoint
        (parameterizedSoninFrame lambda alpha S) +
    (parameterizedSoninFrame lambda alpha S ∘L
        parameterizedSoninGramInv lambda alpha S halpha) ∘L
      ContinuousLinearMap.adjoint
        (parameterizedSoninFrameDerivative lambda alpha S)

/-- The canonical Gram projection path is norm differentiable. -/
theorem hasDerivAt_parameterizedCanonicalGramProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ =>
        parameterizedCanonicalGramProjection lambda beta S)
      (parameterizedCanonicalGramProjectionDerivative
        lambda alpha S halpha) alpha := by
  have hframe := hasDerivAt_parameterizedSoninFrame lambda alpha S
  have hgramInv := hasDerivAt_ringInverse_parameterizedSoninGram
    lambda alpha S halpha
  have hadjoint := HasDerivAt.rectangularAdjoint hframe
  have hleft := HasDerivAt.complexCLMComp hframe hgramInv
  have hall := HasDerivAt.complexCLMComp hleft hadjoint
  simpa only [parameterizedCanonicalGramProjection,
    parameterizedCanonicalGramProjectionDerivative,
    gramCorrectedProjection,
    ringInverse_parameterizedSoninGram lambda alpha S halpha] using hall

/-- Pointwise, the canonical ring-inverse formula is Proof 316's transported
orthogonal projection. -/
theorem parameterizedCanonicalGramProjection_eq_transported
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedCanonicalGramProjection lambda alpha S =
      transportedSoninStarProjection
        (CCM24FiniteSParameterizedEulerEquiv.parameterizedFiniteEulerEquiv
          alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda) := by
  rw [parameterizedCanonicalGramProjection,
    ringInverse_parameterizedSoninGram lambda alpha S halpha]
  rfl

/-!
The finite-S projection can be represented with any nonzero scalar gauge on
the moving frame.  This is the bridge needed to insert the normalized causal
inverse into the complement calculation without multiplying the final Gate
response by the lower Euler factor.
-/
theorem parameterizedCanonicalGramProjection_eq_gaugeNormalized
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1)
    (c : ℂ) (hc : c ≠ 0) :
    gramCorrectedProjection
        (c • parameterizedSoninFrame lambda alpha S)
        (((star c * c)⁻¹) •
          parameterizedSoninGramInv lambda alpha S halpha) =
      parameterizedCanonicalGramProjection lambda alpha S := by
  rw [parameterizedCanonicalGramProjection,
    ringInverse_parameterizedSoninGram lambda alpha S halpha]
  exact gramCorrectedProjection_smul_gauge
    (parameterizedSoninFrame lambda alpha S)
    (parameterizedSoninGramInv lambda alpha S halpha) c hc

/-- The differentiable Gram path is the actual canonical moving Sonin
projection from the parameterized CCM24 transport datum. -/
theorem parameterizedCanonicalGramProjection_eq_soninProjection
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedCanonicalGramProjection lambda alpha S =
      parameterizedSoninProjection lambda alpha S halpha := by
  rw [parameterizedCanonicalGramProjection_eq_transported
    lambda alpha S halpha]
  rw [parameterizedSoninProjection_eq_gramCorrected]
  rfl

end CCM24FiniteSGramProjectionCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
