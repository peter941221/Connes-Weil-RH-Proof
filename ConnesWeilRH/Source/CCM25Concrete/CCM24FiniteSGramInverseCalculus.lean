/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFrameGramCalculus

/-!
# Inversion calculus for the restricted Sonin Gram operator

The exact restricted-transport Gram inverse from Proof 316 is promoted to a
Banach-algebra unit.  Canonical ring inversion can therefore be
differentiated without introducing a stored inverse premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGramInverseCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSFrameGramCalculus
open _root_.ConnesWeilRH.CC20Concrete
open NormedRing ContinuousLinearMap Ring

noncomputable local instance sourceSoninCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Proof 316's exact inverse of the restricted Gram operator. -/
noncomputable def parameterizedSoninGramInv
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  restrictedTransportGramInv
    (parameterizedFiniteEulerEquiv alpha S halpha)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

theorem parameterizedSoninFrame_eq_restrictedClosedTransport
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedSoninFrame lambda alpha S =
      restrictedClosedTransport
        (parameterizedFiniteEulerEquiv alpha S halpha)
        (ccm24ArchimedeanSoninClosedSubspace lambda) := by
  rfl

theorem parameterizedSoninGramInv_mul_gram
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedSoninGramInv lambda alpha S halpha *
        parameterizedSoninGram lambda alpha S = 1 := by
  simpa only [parameterizedSoninGramInv, parameterizedSoninGram,
    parameterizedSoninFrame_eq_restrictedClosedTransport,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
    (restrictedTransportGramInv_leftInverse
      (parameterizedFiniteEulerEquiv alpha S halpha)
      (ccm24ArchimedeanSoninClosedSubspace lambda))

theorem parameterizedSoninGram_isSelfAdjoint
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    IsSelfAdjoint (parameterizedSoninGram lambda alpha S) := by
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self
    (parameterizedSoninFrame lambda alpha S)).isSelfAdjoint

theorem parameterizedSoninGramInv_isSelfAdjoint
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    IsSelfAdjoint (parameterizedSoninGramInv lambda alpha S halpha) :=
  restrictedTransportGramInv_isSelfAdjoint
    (parameterizedFiniteEulerEquiv alpha S halpha)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

theorem parameterizedSoninGram_mul_gramInv
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    parameterizedSoninGram lambda alpha S *
        parameterizedSoninGramInv lambda alpha S halpha = 1 := by
  have h := congrArg star
    (parameterizedSoninGramInv_mul_gram lambda alpha S halpha)
  simpa only [star_mul, star_one,
    (parameterizedSoninGram_isSelfAdjoint lambda alpha S).star_eq,
    (parameterizedSoninGramInv_isSelfAdjoint
      lambda alpha S halpha).star_eq] using h

/-- Concrete unit for the restricted Gram operator. -/
noncomputable def parameterizedSoninGramUnit
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    (sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)ˣ where
  val := parameterizedSoninGram lambda alpha S
  inv := parameterizedSoninGramInv lambda alpha S halpha
  val_inv := parameterizedSoninGram_mul_gramInv lambda alpha S halpha
  inv_val := parameterizedSoninGramInv_mul_gram lambda alpha S halpha

/-- Canonical ring inverse agrees with Proof 316's Gram inverse. -/
theorem ringInverse_parameterizedSoninGram
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    Ring.inverse (parameterizedSoninGram lambda alpha S) =
      parameterizedSoninGramInv lambda alpha S halpha := by
  change Ring.inverse
      ((parameterizedSoninGramUnit lambda alpha S halpha :
        (sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)ˣ) :
        sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) = _
  rw [Ring.inverse_unit]
  rfl

/-- Derivative of the canonical restricted Gram inverse. -/
noncomputable def parameterizedSoninGramInverseDerivative
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  -(parameterizedSoninGramInv lambda alpha S halpha *
      parameterizedSoninGramDerivative lambda alpha S *
      parameterizedSoninGramInv lambda alpha S halpha)

theorem hasDerivAt_ringInverse_parameterizedSoninGram
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) (halpha : |alpha| ≤ 1) :
    HasDerivAt
      (fun beta : ℝ => Ring.inverse
        (parameterizedSoninGram lambda beta S))
      (parameterizedSoninGramInverseDerivative
        lambda alpha S halpha) alpha := by
  have hcanonical :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ)
      (parameterizedSoninGramUnit lambda alpha S halpha))
      |>.comp_hasDerivAt alpha
        (hasDerivAt_parameterizedSoninGram lambda alpha S)
  simpa only [Function.comp_apply, parameterizedSoninGramUnit,
    parameterizedSoninGramInverseDerivative,
    ContinuousLinearMap.neg_apply, mulLeftRight_apply] using hcanonical

end CCM24FiniteSGramInverseCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
