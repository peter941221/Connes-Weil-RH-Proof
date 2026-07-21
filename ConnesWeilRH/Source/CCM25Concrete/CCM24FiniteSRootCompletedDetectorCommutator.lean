/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedSoninCommutator
import Mathlib.Tactic.NoncommRing

/-!
# Completed displacement law through the detector commutator

Orthogonality of the source Sonin projection and quotient band moves the
translation commutator in Proof 466 onto the positive detector.  This leaves
one fixed detector/Sonin commutator followed by the causal translation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorCommutator

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSMultiRenewal
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedSoninCommutator
open CCM24FiniteSTwoSidedRootRecombination

variable {A : Type*} [Ring A]

/-- A band/Sonin off-diagonal corner moves a transport commutator onto the
detector, with the opposite sign. -/
theorem band_detector_transportCommutator_eq_neg_detectorCommutator
    (band detector transport sonin : A)
    (hBandSonin : band * sonin = 0)
    (hSoninBand : sonin * band = 0) :
    band * detector * commutator transport sonin * band =
      -(band * commutator detector sonin * transport * band) := by
  unfold CCM24FiniteSTwoSidedRootRecombination.commutator
  calc
    band * detector * (transport * sonin - sonin * transport) * band =
        band * detector * transport * (sonin * band) -
          band * detector * sonin * transport * band := by noncomm_ring
    _ = -(band * detector * sonin * transport * band) := by
      rw [hSoninBand]
      noncomm_ring
    _ = -(band * detector * sonin * transport * band -
        (band * sonin) * detector * transport * band) := by
      rw [hBandSonin]
      noncomm_ring
    _ = -(band * (detector * sonin - sonin * detector) * transport * band) := by
      noncomm_ring

/-- The completed detector/Sonin crossing at one causal displacement. -/
noncomputable def rootCompletedDetectorSoninTranslationPair
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceBandProjection lambda ∘L
    commutator (detectorOperator owner) (sourceSoninProjection lambda) ∘L
    (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap ∘L
    sourceBandProjection lambda

/-- The root-completed Sonin translation commutator is the negative completed
detector/Sonin crossing. -/
theorem rootCompletedSoninTranslationCommutatorPair_eq_neg_detectorCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    rootCompletedSoninTranslationCommutatorPair owner lambda displacement =
      -rootCompletedDetectorSoninTranslationPair owner lambda displacement := by
  have hBandSonin : sourceBandProjection lambda *
      sourceSoninProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  have hSoninBand : sourceSoninProjection lambda *
      sourceBandProjection lambda = 0 := by
    simpa only [ContinuousLinearMap.mul_def] using
      sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  have hleft :
      (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
          rootConvolution owner =
        sourceBandProjection lambda ∘L detectorOperator owner := by
    rw [ContinuousLinearMap.adjoint_comp,
      (sourceBandProjection_isStarProjection lambda)
        |>.isSelfAdjoint.adjoint_eq,
      detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [rootCompletedSoninTranslationCommutatorPair,
    rootCompletedDetectorSoninTranslationPair]
  let translation :=
    (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap
  let soninCommutator := commutator translation
    (sourceSoninProjection lambda)
  calc
    (rootConvolution owner ∘L sourceBandProjection lambda).adjoint ∘L
          rootConvolution owner ∘L soninCommutator ∘L
          sourceBandProjection lambda =
        sourceBandProjection lambda ∘L detectorOperator owner ∘L
          soninCommutator ∘L sourceBandProjection lambda := by
      apply ContinuousLinearMap.ext
      intro u
      have hu := DFunLike.congr_fun hleft
        (soninCommutator (sourceBandProjection lambda u))
      simpa only [ContinuousLinearMap.comp_apply] using hu
    _ = -(sourceBandProjection lambda ∘L
          commutator (detectorOperator owner)
            (sourceSoninProjection lambda) ∘L
          translation ∘L sourceBandProjection lambda) := by
      simpa only [ContinuousLinearMap.mul_def] using
        band_detector_transportCommutator_eq_neg_detectorCommutator
          (sourceBandProjection lambda) (detectorOperator owner) translation
          (sourceSoninProjection lambda) hBandSonin hSoninBand

/-- The complete finite-Euler corner is the causal probability average of a
single fixed detector/Sonin commutator response. -/
theorem sourceRootCompletedFiniteEulerCorner_eq_detectorTranslationLaw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedFixedQuotientCorner owner lambda
        (radialSupportProjection lambda ∘L
          CCM24FiniteSInverseMetric.normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        (finiteEulerRenewalWeight family.visiblePrimes index : ℂ) •
          rootCompletedDetectorSoninTranslationPair owner lambda
            (finiteEulerRenewalDisplacement family.visiblePrimes index) := by
  rw [sourceRootCompletedFiniteEulerCorner_eq_neg_soninTranslationLaw]
  rw [← tsum_neg]
  apply tsum_congr
  intro index
  rw [rootCompletedSoninTranslationCommutatorPair_eq_neg_detectorCommutator]
  simp only [smul_neg, neg_neg]

end CCM24FiniteSRootCompletedDetectorCommutator
end CCM25Concrete
end Source
end ConnesWeilRH
