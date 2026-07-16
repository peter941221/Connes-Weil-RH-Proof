/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSOrthogonalProjectionFlow

/-!
# Rectangular frame and Gram calculus

The moving Euler transport is restricted to the fixed source Sonin carrier.
Its rectangular adjoint and Gram operator are differentiated in operator
norm, preparing the derivative of the Gram-corrected orthogonal projection.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFrameGramCalculus

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSParameterizedEulerProduct
open CCM24FiniteSParameterizedEulerCalculus

noncomputable local instance sourceSoninCompleteSpace
    (lambda : CCM24SoninScale) :
    CompleteSpace
      (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

section RectangularAdjoint

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Rectangular adjoint as a real linear isometry. -/
noncomputable def rectangularAdjointRealLinearIsometry :
    (E →L[ℂ] F) →ₗᵢ[ℝ] (F →L[ℂ] E) where
  toFun := ContinuousLinearMap.adjoint
  map_add' A B := map_add ContinuousLinearMap.adjoint A B
  map_smul' r A := by
    change ContinuousLinearMap.adjoint ((r : ℂ) • A) =
      (r : ℂ) • ContinuousLinearMap.adjoint A
    rw [map_smulₛₗ]
    simp
  norm_map' A := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint A

@[simp]
theorem rectangularAdjointRealLinearIsometry_apply (A : E →L[ℂ] F) :
    rectangularAdjointRealLinearIsometry A =
      ContinuousLinearMap.adjoint A :=
  rfl

theorem HasDerivAt.rectangularAdjoint
    {f : ℝ → E →L[ℂ] F} {f' : E →L[ℂ] F} {alpha : ℝ}
    (hf : HasDerivAt f f' alpha) :
    HasDerivAt (fun beta => ContinuousLinearMap.adjoint (f beta))
      (ContinuousLinearMap.adjoint f') alpha := by
  simpa only [Function.comp_apply,
    rectangularAdjointRealLinearIsometry_apply] using
    rectangularAdjointRealLinearIsometry.toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt alpha hf

end RectangularAdjoint

/-- Composition of complex-linear maps, regarded as a bounded real bilinear
map on the two complex operator spaces. -/
noncomputable def complexOperatorCompositionReal
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] :
    (F →L[ℂ] G) →L[ℝ] (E →L[ℂ] F) →L[ℝ] (E →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ E F G).bilinearRestrictScalars ℝ

@[simp]
theorem complexOperatorCompositionReal_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F) :
    complexOperatorCompositionReal A B = A ∘L B :=
  rfl

/-- Product rule for composition of complex-linear operator paths with a
real parameter. -/
theorem HasDerivAt.complexCLMComp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : ℝ → F →L[ℂ] G} {f' : F →L[ℂ] G}
    {g : ℝ → E →L[ℂ] F} {g' : E →L[ℂ] F} {alpha : ℝ}
    (hf : HasDerivAt f f' alpha) (hg : HasDerivAt g g' alpha) :
    HasDerivAt (fun beta => f beta ∘L g beta)
      (f' ∘L g alpha + f alpha ∘L g') alpha := by
  let B := complexOperatorCompositionReal (E := E) (F := F) (G := G)
  have hBpath : HasDerivAt (fun _ : ℝ => B) 0 alpha :=
    hasDerivAt_const alpha B
  have houter := hBpath.clm_apply hf
  have hall := houter.clm_apply hg
  simpa only [complexOperatorCompositionReal_apply,
    ContinuousLinearMap.zero_apply, zero_add] using hall

/-- Fixed source Sonin carrier at scale `lambda`. -/
noncomputable abbrev sourceSoninCarrier (lambda : CCM24SoninScale) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule

/-- Rectangular moving frame `A_alpha = T_alpha|S_0`. -/
noncomputable def parameterizedSoninFrame
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  parameterizedFiniteEulerFactor alpha S ∘L
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.subtypeL

/-- Rectangular frame derivative. -/
noncomputable def parameterizedSoninFrameDerivative
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  parameterizedFiniteEulerDerivative alpha S ∘L
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.subtypeL

theorem hasDerivAt_parameterizedSoninFrame
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    HasDerivAt (fun beta : ℝ => parameterizedSoninFrame lambda beta S)
      (parameterizedSoninFrameDerivative lambda alpha S) alpha := by
  have hsubtype : HasDerivAt
      (fun _ : ℝ =>
        (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.subtypeL)
      0 alpha := hasDerivAt_const alpha _
  simpa only [parameterizedSoninFrame,
    parameterizedSoninFrameDerivative,
    ContinuousLinearMap.comp_zero,
    add_zero] using
    (HasDerivAt.complexCLMComp
      (hasDerivAt_parameterizedFiniteEulerFactor alpha S) hsubtype)

/-- Restricted Gram operator `A_alpha^dagger A_alpha`. -/
noncomputable def parameterizedSoninGram
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ContinuousLinearMap.adjoint (parameterizedSoninFrame lambda alpha S) ∘L
    parameterizedSoninFrame lambda alpha S

/-- Product-rule derivative of the restricted Gram operator. -/
noncomputable def parameterizedSoninGramDerivative
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ContinuousLinearMap.adjoint
      (parameterizedSoninFrameDerivative lambda alpha S) ∘L
      parameterizedSoninFrame lambda alpha S +
    ContinuousLinearMap.adjoint
      (parameterizedSoninFrame lambda alpha S) ∘L
      parameterizedSoninFrameDerivative lambda alpha S

theorem hasDerivAt_parameterizedSoninGram
    (lambda : CCM24SoninScale) (alpha : ℝ)
    (S : List CCM24VisiblePrime) :
    HasDerivAt (fun beta : ℝ => parameterizedSoninGram lambda beta S)
      (parameterizedSoninGramDerivative lambda alpha S) alpha := by
  have hframe := hasDerivAt_parameterizedSoninFrame lambda alpha S
  have hadjoint := HasDerivAt.rectangularAdjoint hframe
  simpa only [parameterizedSoninGram,
    parameterizedSoninGramDerivative] using
    (HasDerivAt.complexCLMComp hadjoint hframe)

end CCM24FiniteSFrameGramCalculus
end CCM25Concrete
end Source
end ConnesWeilRH
