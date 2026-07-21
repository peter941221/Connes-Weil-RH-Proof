/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorCompletedKernelOperator

/-!
# Root pairing for the completed detector response

The completed three-branch operator from Proof 474 is identified with the
actual source Sonin commutator.  After the quotient-band compression, its
opposite detector/Sonin orientation factors exactly through the selected
compact convolution root on both sides.  No Hilbert--Schmidt assertion is
made for either raw whole-line root leg.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorRootPairing

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedDetectorCommutator
open CCM24FiniteSRootCompletedDetectorTrace
open CCM24FiniteSRootCompletedDetectorCompletedKernelOperator
open CCM24FiniteSTwoSidedRootRecombination

/-- The compact convolution root after the fixed source quotient band. -/
noncomputable def sourceDetectorBandRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L sourceBandProjection lambda

/-- The same compact root after the translated source Sonin component. -/
noncomputable def sourceDetectorTranslatedSoninRootLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  rootConvolution owner ∘L sourceSoninProjection lambda ∘L
    (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap ∘L
    sourceBandProjection lambda

/-- The complete detector/Sonin displacement atom is the ordered product of
the two compact-root legs.  This is an operator identity, not a separate
estimate of the physical branches. -/
theorem rootCompletedDetectorSoninTranslationPair_eq_rootTraceProduct
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ) :
    rootCompletedDetectorSoninTranslationPair owner lambda displacement =
      (sourceDetectorBandRootLeg owner lambda).adjoint ∘L
        sourceDetectorTranslatedSoninRootLeg owner lambda displacement := by
  have hBandSonin : sourceBandProjection lambda ∘L
      sourceSoninProjection lambda = 0 :=
    sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  rw [rootCompletedDetectorSoninTranslationPair,
    sourceDetectorBandRootLeg, sourceDetectorTranslatedSoninRootLeg,
    ContinuousLinearMap.adjoint_comp,
    (sourceBandProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq,
    detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  apply ContinuousLinearMap.ext
  intro u
  have hzero (v : finiteSCarrier) :
      sourceBandProjection lambda (sourceSoninProjection lambda v) = 0 := by
    have hv := DFunLike.congr_fun hBandSonin v
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] using hv
  simp only [CCM24FiniteSTwoSidedRootRecombination.commutator,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hzero]
  simp only [sub_zero]

/-- Every matrix coefficient of the completed atom is one signed-preserving
cross pairing of the two compact-root legs. -/
theorem rootCompletedDetectorSoninTranslationPair_inner_eq_rootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    (x y : finiteSCarrier) :
    inner ℂ x
        (rootCompletedDetectorSoninTranslationPair owner lambda displacement
          y) =
      inner ℂ (sourceDetectorBandRootLeg owner lambda x)
        (sourceDetectorTranslatedSoninRootLeg owner lambda displacement y) := by
  rw [rootCompletedDetectorSoninTranslationPair_eq_rootTraceProduct,
    ContinuousLinearMap.comp_apply]
  exact (sourceDetectorBandRootLeg owner lambda).adjoint_inner_right x
    (sourceDetectorTranslatedSoninRootLeg owner lambda displacement y)

/-- Proof 474's explicit completed operator is the actual source Sonin
commutator `[R,W]`, not merely an extensionally equivalent branch ledger. -/
theorem sourceCompletedSignedKernelBoundaryOperator_eq_sourceSoninCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor =
      cc20Commutator (sourceSoninProjection lambda)
        (detectorOperator owner) := by
  rw [← sourceThreeBranchPairData_traceProduct_eq_completedKernelOperator owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  exact (sourceSoninCommutator_eq_threeBranch owner lambda).symm

/-- The root pairing attached to one global basis vector and one causal
displacement.  Compact support has acted through the same root on both sides
before any absolute value is introduced. -/
noncomputable def rootCompletedDetectorTranslationRootPairingDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (index : ν) : ℂ :=
  inner ℂ
    (sourceDetectorBandRootLeg owner lambda (globalBasis index))
    (sourceDetectorTranslatedSoninRootLeg owner lambda displacement
      (globalBasis index))

/-- Proof 474's completed physical diagonal is exactly the compact-root cross
pairing.  All outer, reflected, second-support, and prolate cancellation has
already occurred in the commutator before this rewrite. -/
theorem rootCompletedDetectorTranslationCompletedKernelDiagonal_eq_rootPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (index : ν) :
    rootCompletedDetectorTranslationCompletedKernelDiagonal owner lambda
        displacement a c hac hsupp reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor index =
      rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
        displacement globalBasis index := by
  let band := sourceBandProjection lambda
  let translation :=
    (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap
  let commutatorRW := cc20Commutator (sourceSoninProjection lambda)
    (detectorOperator owner)
  have hcompleted :=
    sourceCompletedSignedKernelBoundaryOperator_eq_sourceSoninCommutator owner
      lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  have hbandAdjoint : band.adjoint = band :=
    (sourceBandProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hbandSonin : band ∘L sourceSoninProjection lambda = 0 :=
    sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda
  have hbandZero (z : finiteSCarrier) :
      band (sourceSoninProjection lambda z) = 0 := by
    have hz := DFunLike.congr_fun hbandSonin z
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] using hz
  have hsoninBand : sourceSoninProjection lambda ∘L band = 0 :=
    sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda
  have hsoninAdjoint :
      (sourceSoninProjection lambda).adjoint = sourceSoninProjection lambda :=
    (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq
  have hsoninZero (z : finiteSCarrier) :
      sourceSoninProjection lambda (band z) = 0 := by
    have hz := DFunLike.congr_fun hsoninBand z
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] using hz
  calc
    rootCompletedDetectorTranslationCompletedKernelDiagonal owner lambda
        displacement a c hac hsupp reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor index =
      (-1 : ℂ) * inner ℂ (band (globalBasis index))
        (commutatorRW (translation (band (globalBasis index)))) := by
          unfold rootCompletedDetectorTranslationCompletedKernelDiagonal
          dsimp only [band, translation, commutatorRW]
          rw [hcompleted]
    _ = inner ℂ (globalBasis index)
        (rootCompletedDetectorSoninTranslationPair owner lambda displacement
          (globalBasis index)) := by
          rw [rootCompletedDetectorSoninTranslationPair]
          dsimp only [commutatorRW]
          simp only [cc20Commutator,
            CCM24FiniteSTwoSidedRootRecombination.commutator,
            ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.sub_apply, neg_one_mul]
          have hfirst := hbandZero
            (detectorOperator owner
              (translation (band (globalBasis index))))
          calc
            _ = -(
                inner ℂ (band (globalBasis index))
                  (sourceSoninProjection lambda
                    (detectorOperator owner
                      (translation (band (globalBasis index))))) -
                inner ℂ (band (globalBasis index))
                  (detectorOperator owner
                    (sourceSoninProjection lambda
                      (translation (band (globalBasis index)))))) := by
              rw [inner_sub_right]
            _ = inner ℂ (band (globalBasis index))
                (detectorOperator owner
                  (sourceSoninProjection lambda
                    (translation (band (globalBasis index))))) := by
              rw [show inner ℂ (band (globalBasis index))
                  (sourceSoninProjection lambda
                    (detectorOperator owner
                      (translation (band (globalBasis index))))) = 0 by
                rw [← hsoninAdjoint,
                  (sourceSoninProjection lambda).adjoint_inner_right,
                  hsoninZero]
                simp]
              ring
            _ = inner ℂ (globalBasis index)
                (band.adjoint
                  (detectorOperator owner
                    (sourceSoninProjection lambda
                      (translation (band (globalBasis index)))))) := by
              exact (band.adjoint_inner_right (globalBasis index)
                (detectorOperator owner
                  (sourceSoninProjection lambda
                    (translation (band (globalBasis index)))))).symm
            _ = inner ℂ (globalBasis index)
                (band
                  (detectorOperator owner
                    (sourceSoninProjection lambda
                      (translation (band (globalBasis index)))))) := by
              rw [hbandAdjoint]
            _ = inner ℂ (globalBasis index)
                (band
                  (detectorOperator owner
                    (sourceSoninProjection lambda
                      (translation (band (globalBasis index))))) -
                  band (sourceSoninProjection lambda
                    (detectorOperator owner
                      (translation (band (globalBasis index)))))) := by
              rw [hfirst]
              simp
            _ = _ := by
              dsimp only [band, translation]
              simp only [map_sub]
    _ = rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
        displacement globalBasis index := by
          rw [rootCompletedDetectorSoninTranslationPair_inner_eq_rootPairing]
          rfl

/-- The completed displacement trace is one `tsum` of compact-root cross
pairings.  This is still a signed scalar series; no termwise norm estimate or
trace/renewal exchange is asserted. -/
theorem rootCompletedDetectorSoninTranslationTrace_eq_rootPairing_tsum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    rootCompletedDetectorSoninTranslationTrace owner lambda displacement
        globalBasis =
      ∑' index,
        rootCompletedDetectorTranslationRootPairingDiagonal owner lambda
          displacement globalBasis index := by
  rw [rootCompletedDetectorSoninTranslationTrace_eq_completedKernel_tsum
    owner lambda displacement a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor]
  apply tsum_congr
  intro index
  exact
    rootCompletedDetectorTranslationCompletedKernelDiagonal_eq_rootPairing
      owner lambda displacement a c hac hsupp negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor index

end CCM24FiniteSRootCompletedDetectorRootPairing
end CCM25Concrete
end Source
end ConnesWeilRH
