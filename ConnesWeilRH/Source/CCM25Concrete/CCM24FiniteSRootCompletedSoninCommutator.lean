/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedCommutatorRenewal

/-!
# Translation response as a source-Sonin commutator

The one-parameter response from Proof 465 still displays a quotient-band
commutator.  Orthogonality of the source Sonin projection and its quotient
band converts that corner exactly into the commutator with the fixed source
Sonin projection.  No norm or Schatten assertion is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedSoninCommutator

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedCommutatorRenewal
open CCM24FiniteSTwoSidedRootRecombination

/-- The source-Sonin corner of the quotient-band commutator is the negative
source-Sonin projection commutator on the quotient input. -/
theorem sourceSonin_bandCommutator_band_eq_neg_soninCommutator
    (lambda : CCM24SoninScale)
    (transport : finiteSCarrier →L[ℂ] finiteSCarrier) :
    sourceSoninProjection lambda ∘L
        commutator transport (sourceBandProjection lambda) ∘L
        sourceBandProjection lambda =
      -(commutator transport (sourceSoninProjection lambda) ∘L
        sourceBandProjection lambda) := by
  apply ContinuousLinearMap.ext
  intro u
  have hBsq :
      sourceBandProjection lambda
          (sourceBandProjection lambda u) = sourceBandProjection lambda u := by
    have h := DFunLike.congr_fun
      ((sourceBandProjection_isStarProjection lambda).isIdempotentElem) u
    simpa only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply] using h
  have hPB :
      sourceSoninProjection lambda (sourceBandProjection lambda u) = 0 := by
    exact DFunLike.congr_fun
      (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda) u
  have hPBtransport :
      sourceSoninProjection lambda
          (sourceBandProjection lambda
            (transport (sourceBandProjection lambda u))) = 0 := by
    exact DFunLike.congr_fun
      (sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)
      (transport (sourceBandProjection lambda u))
  simp only [ContinuousLinearMap.comp_apply,
    CCM24FiniteSTwoSidedRootRecombination.commutator,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, map_sub]
  rw [hBsq, hPB, hPBtransport, map_zero]
  abel

/-- The completed response built from the translation commutator with the
fixed source Sonin projection. -/
noncomputable def rootCompletedSoninTranslationCommutatorPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
    rootConvolution owner ∘L
    commutator
      (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap
      (sourceSoninProjection lambda) ∘L
    sourceBandProjection lambda

/-- Proof 465's unweighted displacement response is a completed commutator
with the fixed source Sonin projection. -/
theorem rootCompletedTranslationCommutatorPair_eq_neg_soninCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    rootCompletedTranslationCommutatorPair owner lambda displacement =
      -rootCompletedSoninTranslationCommutatorPair owner lambda
        displacement := by
  rw [rootCompletedTranslationCommutatorPair,
    rootCompletedBandCommutatorTransform_apply,
    sourceSonin_bandCommutator_band_eq_neg_soninCommutator]
  unfold rootCompletedSoninTranslationCommutatorPair
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg]

/-- The complete finite-Euler corner is the negative probability average of
one fixed source-Sonin translation-commutator response. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_neg_soninTranslationLaw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          CCM24FiniteSInverseMetric.normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      -(∑' index : CCM24FiniteSMultiRenewal.FiniteEulerRenewalIndex
            family.visiblePrimes,
        (CCM24FiniteSMultiRenewal.finiteEulerRenewalWeight
            family.visiblePrimes index : ℂ) •
          rootCompletedSoninTranslationCommutatorPair owner lambda
            (CCM24FiniteSMultiRenewal.finiteEulerRenewalDisplacement
              family.visiblePrimes index)) := by
  rw [sourceRootCompletedFiniteEulerCorner_eq_weightedTranslationLaw]
  rw [← tsum_neg]
  apply tsum_congr
  intro index
  rw [rootCompletedTranslationCommutatorPair_eq_neg_soninCommutator]
  simp only [smul_neg]

end CCM24FiniteSRootCompletedSoninCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
