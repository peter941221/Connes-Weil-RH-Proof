/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalRenewalExpansion
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCausalCoframe

/-!
# Ordered causal Gram owner for the finite-S response

This file gives the existing finite-S source-carrier response the ordered
causal names used by the Gate 3U ledger.  The source coordinate is literal:

```text
K_S       = T_S J
Gamma_S   = K_S† K_S
N_W       = K_S† W K_S - W_0 Gamma_S
response  = N_W Gamma_S⁻¹
```

Here `J` is the source Sonin inclusion, `T_S` is the actual finite Euler
transport, and `W_0 = J† W J`.  This is a source-coordinate realization of
the ordered Gram response.  It is deliberately not an assertion that this
`K_S` is the ambient `E T_S⁻¹ B` from the causal shorted-covariance model;
that carrier identification still needs its own producer.

The module therefore closes the exact algebraic ownership and the physical
three-branch/causal-renewal readback, while keeping the missing uniform signed
estimate explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSOrderedCausalGram

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCoframeResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSPhysicalRenewalExpansion
open CCM24FiniteSForwardRenewal
open CCM24FiniteSMultiRenewal
open scoped InnerProduct

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! The four ordered objects. -/

/-- The source-coordinate causal frame `K_S = T_S J`. -/
noncomputable def sourceOrderedCausalK
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  finiteEulerFrame lambda family

/-- The ordered causal Gram covariance `Gamma_S = K_S† K_S`. -/
noncomputable def sourceOrderedCausalGamma
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceOrderedCausalK lambda family)† ∘L
    sourceOrderedCausalK lambda family

/-- The source-coordinate detector compression `W_0 = J† W J`. -/
noncomputable def sourceOrderedCausalDetector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
    sourceInclusion lambda

/-- The ordered numerator `N_W = K_S† W K_S - W_0 Gamma_S`. -/
noncomputable def sourceOrderedCausalNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceOrderedCausalK lambda family)† ∘L detectorOperator owner ∘L
      sourceOrderedCausalK lambda family -
    sourceOrderedCausalDetector owner lambda ∘L
      sourceOrderedCausalGamma lambda family

/-- The exact inverse of the ordered Gram covariance. -/
noncomputable def sourceOrderedCausalGammaInv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  finiteEulerGramInv lambda family

/-- The ordered relative response `N_W Gamma_S⁻¹`. -/
noncomputable def sourceOrderedCausalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  sourceOrderedCausalNumerator owner lambda family ∘L
    sourceOrderedCausalGammaInv lambda family

theorem sourceOrderedCausalK_eq_finiteEulerFrame
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalK lambda family = finiteEulerFrame lambda family := rfl

theorem sourceOrderedCausalK_eq_transport_comp_inclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalK lambda family =
      (ccm24FiniteEulerTransportEquiv family.visiblePrimes).toContinuousLinearMap ∘L
        sourceInclusion lambda := by
  exact finiteEulerFrame_eq_transport_comp_inclusion lambda family

theorem sourceOrderedCausalGamma_eq_finiteEulerGram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalGamma lambda family = finiteEulerGram lambda family := rfl

theorem sourceOrderedCausalGammaInv_comp_gamma
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalGammaInv lambda family ∘L
        sourceOrderedCausalGamma lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  exact finiteEulerGramInv_comp_gram lambda family

theorem sourceOrderedCausalGamma_comp_gammaInv
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalGamma lambda family ∘L
        sourceOrderedCausalGammaInv lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  exact finiteEulerGram_comp_inv lambda family

theorem sourceOrderedCausalGamma_isSelfAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    IsSelfAdjoint (sourceOrderedCausalGamma lambda family) := by
  exact finiteEulerGram_isSelfAdjoint lambda family

theorem sourceOrderedCausalGamma_isPositive
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceOrderedCausalGamma lambda family).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (sourceOrderedCausalK lambda family)

/-- The same ordered frame and Gram inverse produce the actual target
orthogonal Sonin projection. -/
theorem targetSoninProjection_eq_sourceOrderedCausalGramProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetSoninProjection lambda family =
      sourceOrderedCausalK lambda family ∘L
        sourceOrderedCausalGammaInv lambda family ∘L
          (sourceOrderedCausalK lambda family)† := by
  rw [targetSoninProjection_eq_dualFrame_comp_frameAdjoint,
    finiteEulerDualFrame]
  rfl

theorem sourceOrderedCausalNumerator_eq_centeredGramNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalNumerator owner lambda family =
      centeredGramNumerator owner lambda family := by
  rfl

/-- The ordered owner reads back to the already legal algebraic response
`sourceGramResponse`; no trace cycle is used in this theorem. -/
theorem sourceOrderedCausalResponse_eq_sourceGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalResponse owner lambda family =
      sourceGramResponse owner lambda family := by
  change centeredGramNumerator owner lambda family ∘L
      finiteEulerGramInv lambda family =
    sourceGramResponse owner lambda family
  exact (sourceGramResponse_eq_centered owner lambda family).symm

/-- The route-band sign is exact: the ordered source response is the negative
of the projection-band response. -/
theorem sourceOrderedCausalResponse_eq_neg_sourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalResponse owner lambda family =
      -CCM24FiniteSBandTrace.sourceBandGramResponse owner lambda family := by
  rw [sourceOrderedCausalResponse_eq_sourceGramResponse,
    CCM24FiniteSBandTrace.sourceBandGramResponse]
  simp

/-- The complete three-branch physical numerator remains before the ordered
Gram inverse. -/
theorem sourceOrderedCausalNumerator_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalNumerator owner lambda family =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda)
          (detectorOperator owner) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda := by
  change centeredGramNumerator owner lambda family = _
  exact centeredGramNumerator_eq_threeBranch owner lambda family

/-- Exact response readback after the common ordered inverse Gram leg. -/
theorem sourceOrderedCausalResponse_eq_threeBranch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalResponse owner lambda family =
      (sourceInclusion lambda)† ∘L
        cc20ThreeBranchCommutator
          (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda)
          (detectorOperator owner) ∘L
        finiteEulerAmbientGram family ∘L sourceInclusion lambda ∘L
          finiteEulerGramInv lambda family := by
  rw [sourceOrderedCausalResponse_eq_sourceGramResponse]
  exact sourceGramResponse_eq_threeBranch owner lambda family

/-- The same ordered response in coframe coordinates.  This is the exact
source-side form in which the physical leakage is visible. -/
theorem sourceOrderedCausalResponse_eq_detector_coframe_difference
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalResponse owner lambda family =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        (finiteEulerMetricCoframe lambda family - sourceInclusion lambda) := by
  rw [sourceOrderedCausalResponse_eq_sourceGramResponse,
    sourceGramResponse, frameAdjoint_detector_frame_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    map_sub]
  rfl

/-- The coframe difference is exactly the completed three-branch leakage. -/
theorem sourceOrderedCausalResponse_eq_detector_physical_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceOrderedCausalResponse owner lambda family =
      (sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        sourcePhysicalCoframeLeakage lambda family := by
  rw [sourceOrderedCausalResponse_eq_detector_coframe_difference,
    ← sourceSoninCoframeLeakage_eq_physical,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion]

/-! The scalar gauge is kept on the complete owner. -/

/-- The gauged source frame.  The scalar is inserted into the frame, not
multiplied onto the final response. -/
noncomputable def gaugedSourceOrderedCausalK
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  c • sourceOrderedCausalK lambda family

/-- The Gram covariance of the gauged frame. -/
noncomputable def gaugedSourceOrderedCausalGamma
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (gaugedSourceOrderedCausalK c lambda family)† ∘L
    gaugedSourceOrderedCausalK c lambda family

/-- The explicit inverse Gram covariance after a nonzero scalar gauge. -/
noncomputable def gaugedSourceOrderedCausalGammaInv
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ((star c * c)⁻¹) • sourceOrderedCausalGammaInv lambda family

/-- The gauged centered numerator. -/
noncomputable def gaugedSourceOrderedCausalNumerator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (gaugedSourceOrderedCausalK c lambda family)† ∘L detectorOperator owner ∘L
      gaugedSourceOrderedCausalK c lambda family -
    sourceOrderedCausalDetector owner lambda ∘L
      gaugedSourceOrderedCausalGamma c lambda family

/-- The gauged ordered response, with the inverse Gram factor kept paired with
the gauged numerator. -/
noncomputable def gaugedSourceOrderedCausalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  gaugedSourceOrderedCausalNumerator owner c lambda family ∘L
    gaugedSourceOrderedCausalGammaInv c lambda family

theorem gaugedSourceOrderedCausalGamma_eq_scalar
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalGamma c lambda family =
      (star c * c) • sourceOrderedCausalGamma lambda family := by
  have hAdj :
      ContinuousLinearMap.adjoint (c • sourceOrderedCausalK lambda family) =
        (star c) • ContinuousLinearMap.adjoint
          (sourceOrderedCausalK lambda family) := by
    simpa only [starRingEnd_apply] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ c
        (sourceOrderedCausalK lambda family))
  apply ContinuousLinearMap.ext
  intro u
  simp only [gaugedSourceOrderedCausalGamma, gaugedSourceOrderedCausalK,
    map_smulₛₗ _, starRingEnd_apply, RingHom.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, smul_smul]
  rw [hAdj]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul,
    sourceOrderedCausalGamma]
  rw [mul_comm]
  rfl

theorem gaugedSourceOrderedCausalNumerator_eq_scalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (c : ℂ) (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalNumerator owner c lambda family =
      (star c * c) • sourceOrderedCausalNumerator owner lambda family := by
  have hAdj :
      ContinuousLinearMap.adjoint (c • sourceOrderedCausalK lambda family) =
        (star c) • ContinuousLinearMap.adjoint
          (sourceOrderedCausalK lambda family) := by
    simpa only [starRingEnd_apply] using
      (ContinuousLinearMap.adjoint.map_smulₛₗ c
        (sourceOrderedCausalK lambda family))
  apply ContinuousLinearMap.ext
  intro u
  simp only [gaugedSourceOrderedCausalNumerator,
    gaugedSourceOrderedCausalK, sourceOrderedCausalNumerator,
    sourceOrderedCausalDetector, gaugedSourceOrderedCausalGamma,
    sourceOrderedCausalGamma, map_smulₛₗ _, starRingEnd_apply,
    RingHom.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [hAdj]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul,
    smul_sub]
  rw [mul_comm]

theorem gaugedSourceOrderedCausalGammaInv_comp_gamma
    (c : ℂ) (hc : c ≠ 0) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalGammaInv c lambda family ∘L
        gaugedSourceOrderedCausalGamma c lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hstar : star c ≠ 0 := by
    intro hzero
    apply hc
    simpa using congrArg star hzero
  have hscalar : star c * c ≠ 0 := mul_ne_zero hstar hc
  rw [gaugedSourceOrderedCausalGamma_eq_scalar]
  apply ContinuousLinearMap.ext
  intro u
  simp only [gaugedSourceOrderedCausalGammaInv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [mul_inv_cancel₀ hscalar, one_smul]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrFun (congrArg DFunLike.coe
      (sourceOrderedCausalGammaInv_comp_gamma lambda family)) u

theorem gaugedSourceOrderedCausalGamma_comp_gammaInv
    (c : ℂ) (hc : c ≠ 0) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalGamma c lambda family ∘L
        gaugedSourceOrderedCausalGammaInv c lambda family =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
  have hstar : star c ≠ 0 := by
    intro hzero
    apply hc
    simpa using congrArg star hzero
  have hscalar : star c * c ≠ 0 := mul_ne_zero hstar hc
  rw [gaugedSourceOrderedCausalGamma_eq_scalar]
  apply ContinuousLinearMap.ext
  intro u
  simp only [gaugedSourceOrderedCausalGammaInv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [inv_mul_cancel₀ hscalar, one_smul]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
    congrFun (congrArg DFunLike.coe
      (sourceOrderedCausalGamma_comp_gammaInv lambda family)) u

/-- Scalar gauge invariance of the complete ordered response. -/
theorem gaugedSourceOrderedCausalResponse_eq_sourceOrderedCausalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (c : ℂ) (hc : c ≠ 0) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalResponse owner c lambda family =
      sourceOrderedCausalResponse owner lambda family := by
  have hstar : star c ≠ 0 := by
    intro hzero
    apply hc
    simpa using congrArg star hzero
  have hscalar : star c * c ≠ 0 := mul_ne_zero hstar hc
  rw [gaugedSourceOrderedCausalResponse,
    gaugedSourceOrderedCausalNumerator_eq_scalar,
    gaugedSourceOrderedCausalGammaInv]
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceOrderedCausalResponse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul]
  rw [inv_mul_cancel₀ hscalar, one_smul]

theorem lowerFactorGaugedSourceOrderedCausalResponse_eq_sourceOrderedCausalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalResponse owner
        (finiteEulerLowerFactor family.visiblePrimes : ℂ)
        lambda family =
      sourceOrderedCausalResponse owner lambda family := by
  exact gaugedSourceOrderedCausalResponse_eq_sourceOrderedCausalResponse owner
    (finiteEulerLowerFactor family.visiblePrimes : ℂ)
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes)))
    lambda family

theorem lowerFactorGaugedSourceOrderedCausalResponse_eq_neg_gaugedSourceCycledBand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    gaugedSourceOrderedCausalResponse owner
        (finiteEulerLowerFactor family.visiblePrimes : ℂ)
        lambda family =
      -finiteEulerLowerFactorGaugedSourceCycledBandResponse
        owner lambda family := by
  rw [lowerFactorGaugedSourceOrderedCausalResponse_eq_sourceOrderedCausalResponse,
    sourceOrderedCausalResponse_eq_neg_sourceBandGramResponse,
    sourceBandGramResponse_eq_finiteEulerLowerFactorGaugedSourceCycledBandResponse]

/-! The lower-factor-scaled response is a different object: it is the
condition-number-free normalized physical response, not the gauge-invariant
ordered response above. -/

/-- The condition-number-free scaled ordered response. -/
noncomputable def lowerFactorScaledSourceOrderedCausalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2) •
    sourceOrderedCausalResponse owner lambda family

theorem lowerFactorScaledSourceOrderedCausalResponse_eq_neg_normalizedBand
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorScaledSourceOrderedCausalResponse owner lambda family =
      -CCM24FiniteSNormalizedPhysicalResponse.normalizedSourceBandGramResponse
        owner lambda family := by
  rw [lowerFactorScaledSourceOrderedCausalResponse,
    normalizedSourceBandGramResponse,
    sourceOrderedCausalResponse_eq_neg_sourceBandGramResponse]
  simp only [smul_neg, neg_neg]

/-- The causal renewal expansion belongs to the complete ordered owner, with
the physical response atoms still assembled before estimation. -/
theorem lowerFactorScaledSourceOrderedCausalResponse_eq_neg_renewalExpansion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    lowerFactorScaledSourceOrderedCausalResponse owner lambda family =
      -(∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalResponseAtom owner lambda family forwardIndex
            renewalIndex) := by
  rw [lowerFactorScaledSourceOrderedCausalResponse_eq_neg_normalizedBand,
    normalizedSourceBandGramResponse_eq_renewalExpansion]

/-! The exact raw readback keeps the lower-factor inverse outside the complete
physical renewal sum.  This is the raw scalar-gauged owner; no branchwise norm
or trace estimate is introduced by this identity. -/
theorem sourceBandGramResponse_eq_inv_lowerFactor_sq_smul_renewalExpansion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ •
        (∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
          ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
            finiteEulerPhysicalResponseAtom owner lambda family forwardIndex
              renewalIndex) := by
  have hc : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  have hscale :
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ •
          CCM24FiniteSNormalizedPhysicalResponse.normalizedSourceBandGramResponse
            owner lambda family =
        sourceBandGramResponse owner lambda family := by
    rw [CCM24FiniteSNormalizedPhysicalResponse.normalizedSourceBandGramResponse]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    field_simp [hc] <;> simp
  rw [← hscale,
    CCM24FiniteSPhysicalRenewalExpansion.normalizedSourceBandGramResponse_eq_renewalExpansion]

theorem finiteEulerLowerFactorGaugedSourceCycledBandResponse_eq_inv_lowerFactor_sq_smul_renewalExpansion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerLowerFactorGaugedSourceCycledBandResponse owner lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ •
        (∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
          ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
            finiteEulerPhysicalResponseAtom owner lambda family forwardIndex
              renewalIndex) := by
  rw [← sourceBandGramResponse_eq_finiteEulerLowerFactorGaugedSourceCycledBandResponse
    owner lambda family]
  exact sourceBandGramResponse_eq_inv_lowerFactor_sq_smul_renewalExpansion
    owner lambda family

/-- The exact uniform statement currently available at the normalized level.
It is intentionally not divided by the Euler lower factor. -/
theorem norm_lowerFactorScaledSourceOrderedCausalResponse_le_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖lowerFactorScaledSourceOrderedCausalResponse owner lambda family‖ ≤
      ‖detectorOperator owner‖ := by
  rw [lowerFactorScaledSourceOrderedCausalResponse_eq_neg_normalizedBand]
  simpa only [norm_neg] using
    (norm_normalizedSourceBandGramResponse_le_detector owner lambda family)

end CCM24FiniteSOrderedCausalGram
end CCM25Concrete
end Source
end ConnesWeilRH
