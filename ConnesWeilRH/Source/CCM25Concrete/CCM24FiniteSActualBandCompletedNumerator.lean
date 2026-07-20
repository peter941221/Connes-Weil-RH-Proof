/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSOrderedCausalGram

/-!
# Completed relative numerator for the actual finite-S band remainder

Proof 441 identifies the legal nonlinear remainder with a four-leg quadratic
cycle on the source Sonin carrier.  The ordered Gram owner supplies the
relative numerator for the nonlinear endpoint.  This module combines the
correctly oriented first jet and that endpoint numerator before the common
inverse Gram leg is applied.

The resulting completed numerator is exact and scalar-gauge invariant after
it is paired with the matching inverse Gram covariance.  No trace estimate,
positivity statement, Gate 3U bound, or RH premise is stored here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualBandCompletedNumerator

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSOrderedCausalGram

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-- The first jet and the ordered endpoint numerator with the common Gram
covariance kept on the right of the first jet. -/
noncomputable def actualBandCompletedRelativeNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  actualBandFirstJetCycledResponse owner lambda family ∘L
      sourceOrderedCausalGamma lambda family +
    sourceOrderedCausalNumerator owner lambda family

/-- Multiplying the route-oriented endpoint by its Gram covariance removes
the inverse Gram leg and leaves the negative ordered numerator. -/
theorem sourceBandGramResponse_comp_gamma_eq_neg_numerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family ∘L
        sourceOrderedCausalGamma lambda family =
      -sourceOrderedCausalNumerator owner lambda family := by
  rw [sourceBandGramResponse, sourceGramResponse_eq_centered,
    sourceOrderedCausalNumerator_eq_centeredGramNumerator]
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : SourceOp lambda => operator u)
    (sourceOrderedCausalGammaInv_comp_gamma lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hu
  change -centeredGramNumerator owner lambda family
      (sourceOrderedCausalGammaInv lambda family
        (sourceOrderedCausalGamma lambda family u)) =
    -centeredGramNumerator owner lambda family u
  rw [hu]

/-- The completed numerator is exactly the quadratic-cycle response followed
by the same Gram covariance. -/
theorem actualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualBandCompletedRelativeNumerator owner lambda family =
      actualBandQuadraticCycledResponse owner lambda family ∘L
        sourceOrderedCausalGamma lambda family := by
  rw [actualBandCompletedRelativeNumerator,
    actualBandQuadraticCycledResponse,
    ← sourceBandGramResponse_eq_endpointCycle]
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : SourceOp lambda => operator u)
    (sourceBandGramResponse_comp_gamma_eq_neg_numerator owner lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply] at hu ⊢
  rw [hu]
  abel

/-- Applying the matching inverse Gram covariance reads the completed
numerator back as the actual quadratic cycle. -/
theorem actualBandCompletedRelativeNumerator_comp_gammaInv_eq_quadraticCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualBandCompletedRelativeNumerator owner lambda family ∘L
        sourceOrderedCausalGammaInv lambda family =
      actualBandQuadraticCycledResponse owner lambda family := by
  rw [actualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma]
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : SourceOp lambda => operator u)
    (sourceOrderedCausalGamma_comp_gammaInv lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hu ⊢
  rw [hu]

/-- The un-gauged completed relative response. -/
noncomputable def actualBandCompletedRelativeResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  actualBandCompletedRelativeNumerator owner lambda family ∘L
    sourceOrderedCausalGammaInv lambda family

/-- The same-carrier nonlinear remainder is exactly the completed relative
response, with no ambient trace cycle or stored premise. -/
theorem sourceActualBandFiniteEulerRemainderResponse_eq_completedRelativeResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceActualBandFiniteEulerRemainderResponse owner lambda family =
      actualBandCompletedRelativeResponse owner lambda family := by
  rw [actualBandCompletedRelativeResponse,
    actualBandCompletedRelativeNumerator_comp_gammaInv_eq_quadraticCycle,
    sourceActualBandFiniteEulerRemainderResponse_eq_quadraticCycle]

/-- The completed numerator exposes the ordered three-branch numerator after
the first-jet Gram leg is added. -/
theorem actualBandCompletedRelativeNumerator_eq_firstJet_gram_add_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    actualBandCompletedRelativeNumerator owner lambda family =
      actualBandFirstJetCycledResponse owner lambda family ∘L
          sourceOrderedCausalGamma lambda family +
        (ContinuousLinearMap.adjoint (sourceInclusion lambda) ∘L
          cc20ThreeBranchCommutator
            (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda)
            (detectorOperator owner) ∘L
          finiteEulerAmbientGram family ∘L sourceInclusion lambda) := by
  rw [actualBandCompletedRelativeNumerator,
    sourceOrderedCausalNumerator_eq_threeBranch]

/-- The same completed numerator after a paired scalar rescaling of the
ordered frame and inverse Gram covariance. -/
noncomputable def gaugedActualBandCompletedRelativeNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (c : ℂ)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  actualBandFirstJetCycledResponse owner lambda family ∘L
      gaugedSourceOrderedCausalGamma c lambda family +
    gaugedSourceOrderedCausalNumerator owner c lambda family

/-- Both terms of the completed numerator acquire the same scalar under the
paired gauge. -/
theorem gaugedActualBandCompletedRelativeNumerator_eq_scalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (c : ℂ)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedActualBandCompletedRelativeNumerator owner c lambda family =
      (star c * c) •
        actualBandCompletedRelativeNumerator owner lambda family := by
  rw [gaugedActualBandCompletedRelativeNumerator,
    actualBandCompletedRelativeNumerator,
    gaugedSourceOrderedCausalGamma_eq_scalar,
    gaugedSourceOrderedCausalNumerator_eq_scalar]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_smul,
    smul_add]

/-- The gauged completed numerator remains the quadratic cycle followed by
the correspondingly gauged Gram covariance. -/
theorem gaugedActualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (c : ℂ)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedActualBandCompletedRelativeNumerator owner c lambda family =
      actualBandQuadraticCycledResponse owner lambda family ∘L
        gaugedSourceOrderedCausalGamma c lambda family := by
  rw [gaugedActualBandCompletedRelativeNumerator_eq_scalar,
    actualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma,
    gaugedSourceOrderedCausalGamma_eq_scalar]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul]

/-- The complete paired response in the chosen scalar gauge. -/
noncomputable def gaugedActualBandCompletedRelativeResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (c : ℂ)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    SourceOp lambda :=
  gaugedActualBandCompletedRelativeNumerator owner c lambda family ∘L
    gaugedSourceOrderedCausalGammaInv c lambda family

/-- Paired scalar normalization changes neither the completed physical
response nor its operator ordering. -/
theorem gaugedActualBandCompletedRelativeResponse_eq_quadraticCycle
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (c : ℂ) (hc : c ≠ 0)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedActualBandCompletedRelativeResponse owner c lambda family =
      actualBandQuadraticCycledResponse owner lambda family := by
  rw [gaugedActualBandCompletedRelativeResponse,
    gaugedActualBandCompletedRelativeNumerator_eq_quadraticCycle_comp_gamma]
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg
    (fun operator : SourceOp lambda => operator u)
    (gaugedSourceOrderedCausalGamma_comp_gammaInv c hc lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hu ⊢
  rw [hu]

end CCM24FiniteSActualBandCompletedNumerator
end CCM25Concrete
end Source
end ConnesWeilRH
