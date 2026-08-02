/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPulledObliqueReduction

/-!
# Square-zero oblique-shear reduction for the finite-S Gate trace

The pulled target projection has the same range as the source Sonin
projection.  Their difference is therefore a single square-zero off-diagonal
block.  The active target response is exactly the detector paired with this
block.

No norm bound for the oblique shear or family-uniform Gate estimate is
asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalObliqueShearReduction

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSActualBandJetOrientation
open CCM24FiniteSGatePhysicalSignedDiagonal
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSGatePhysicalPulledObliqueReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSCausalSupport
open CCM24FiniteSInverseMetric
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Pulling the actual target projection back gives the lifted restricted
Gram inverse followed by the ambient Gram.  This formula is used only to
certify the range, not for a factorwise estimate. -/
theorem finiteEulerPulledTargetProjection_eq_sourceGramInvAmbient_comp_gram
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledTargetProjection lambda family =
      finiteEulerSourceGramInvAmbient lambda family ∘L
        finiteEulerAmbientGram family := by
  rw [finiteEulerPulledTargetProjection,
    targetSoninProjection_eq_ambientGramProjection]
  apply ContinuousLinearMap.ext
  intro u
  have hInverse := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (finiteEulerSourceGramInvAmbient lambda family
        (((finiteEulerTransportOperator family)†)
          (finiteEulerTransportOperator family u))))
    (inverse_comp_transport family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hInverse
  simp only [ContinuousLinearMap.comp_apply]
  rw [hInverse]
  rfl

/-- The range of the pulled target projection is contained in the source
Sonin range: `R Q_S=Q_S`. -/
theorem sourceSoninProjection_comp_finiteEulerPulledTargetProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        finiteEulerPulledTargetProjection lambda family =
      finiteEulerPulledTargetProjection lambda family := by
  rw [finiteEulerPulledTargetProjection_eq_sourceGramInvAmbient_comp_gram]
  apply ContinuousLinearMap.ext
  intro u
  have hRange := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (finiteEulerAmbientGram family u))
    (sourceSoninProjection_comp_sourceGramInvAmbient lambda family)
  simpa only [ContinuousLinearMap.comp_apply] using hRange

/-- The one off-diagonal finite-S block `N_S=Q_S-R`. -/
noncomputable def finiteEulerPulledObliqueShear
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  finiteEulerPulledTargetProjection lambda family -
    sourceSoninProjection lambda

/-- The shear lands in the source Sonin range: `R N_S=N_S`. -/
theorem sourceSoninProjection_comp_finiteEulerPulledObliqueShear
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        finiteEulerPulledObliqueShear lambda family =
      finiteEulerPulledObliqueShear lambda family := by
  have hRange :=
    sourceSoninProjection_comp_finiteEulerPulledTargetProjection
      lambda family
  have hProjectionSq :
      sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
        sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  apply ContinuousLinearMap.ext
  intro u
  have hRangeApply := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    hRange
  have hProjectionSqApply := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    hProjectionSq
  simp only [finiteEulerPulledObliqueShear,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  simp only [ContinuousLinearMap.comp_apply] at hRangeApply hProjectionSqApply
  rw [hRangeApply, hProjectionSqApply]

/-- The shear vanishes on the source Sonin range: `N_S R=0`. -/
theorem finiteEulerPulledObliqueShear_comp_sourceSoninProjection_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledObliqueShear lambda family ∘L
        sourceSoninProjection lambda = 0 := by
  have hFix :=
    finiteEulerPulledTargetProjection_comp_sourceSoninProjection
      lambda family
  have hProjectionSq :
      sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
        sourceSoninProjection lambda := by
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
  apply ContinuousLinearMap.ext
  intro u
  have hFixApply := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    hFix
  have hProjectionSqApply := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    hProjectionSq
  simp only [finiteEulerPulledObliqueShear,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply]
  simp only [ContinuousLinearMap.comp_apply] at hFixApply hProjectionSqApply
  rw [hFixApply, hProjectionSqApply, sub_self]

/-- The oblique shear is square-zero: `N_S^2=0`. -/
theorem finiteEulerPulledObliqueShear_comp_self_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledObliqueShear lambda family ∘L
        finiteEulerPulledObliqueShear lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hRange := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (sourceSoninProjection_comp_finiteEulerPulledObliqueShear
      lambda family)
  have hZero := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (finiteEulerPulledObliqueShear lambda family u))
    (finiteEulerPulledObliqueShear_comp_sourceSoninProjection_eq_zero
      lambda family)
  simp only [ContinuousLinearMap.comp_apply] at hRange
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hZero ⊢
  rw [← hRange, hZero]

/-- The shear is precisely the source/complement crossing
`R Q_S (I-R)`. -/
theorem finiteEulerPulledObliqueShear_eq_sourceCrossing
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledObliqueShear lambda family =
      sourceSoninProjection lambda ∘L
        finiteEulerPulledTargetProjection lambda family ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceSoninProjection lambda) := by
  apply ContinuousLinearMap.ext
  intro u
  have hRange := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (sourceSoninProjection_comp_finiteEulerPulledTargetProjection
      lambda family)
  have hFix := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (finiteEulerPulledTargetProjection_comp_sourceSoninProjection
      lambda family)
  have hRangeOnSource := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (sourceSoninProjection lambda u))
    (sourceSoninProjection_comp_finiteEulerPulledTargetProjection
      lambda family)
  simp only [ContinuousLinearMap.comp_apply] at hRange hFix hRangeOnSource
  simp only [finiteEulerPulledObliqueShear,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hRange, hRangeOnSource, hFix]

/-- The active response written against the one square-zero shear. -/
noncomputable def finiteEulerPulledObliqueShearResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourceInclusion lambda)† ∘L
    finiteEulerPulledObliqueShear lambda family ∘L
      detectorOperator owner ∘L sourceInclusion lambda

/-- The actual target response is exactly `J† N_S W J`. -/
theorem finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerPulledObliqueShearResponse owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_pulledProjectionDifference]
  apply ContinuousLinearMap.ext
  intro u
  have hAdjointSource := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda u)))
    (sourceInclusionAdjoint_comp_sourceProjection lambda)
  simp only [finiteEulerPulledObliqueShearResponse,
    finiteEulerPulledObliqueShear, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  simp only [ContinuousLinearMap.comp_apply] at hAdjointSource
  rw [hAdjointSource]

/-- Proof 744's fixed-source commutator response equals the one-shear
response, again without a trace cycle. -/
theorem finiteEulerPulledSourceCommutatorResponse_eq_obliqueShear
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledSourceCommutatorResponse owner lambda family =
      finiteEulerPulledObliqueShearResponse owner lambda family :=
  (finiteEulerTargetCommutatorResponse_eq_pulledSourceCommutator
    owner lambda family).symm.trans
      (finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear
        owner lambda family)

/-- Uniform target-response boundedness is exactly uniform boundedness of the
one square-zero shear response. -/
theorem exists_uniform_targetCommutatorTraceBound_iff_obliqueShearBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerPulledObliqueShearResponse
          owner lambda family)‖ ≤ bound) := by
  simp only [finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear]

/-- The Gate reduction now lands on the single source/complement shear block.
No bound for that block is asserted. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_obliqueShearBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu sigma rho : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerPulledObliqueShearResponse
          owner lambda family)‖ ≤ bound) := by
  calc
    _ ↔ ∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
        ‖ordinaryTraceAlong sourceBasis
          (finiteEulerTargetCommutatorResponse
            owner lambda family)‖ ≤ bound :=
      exists_uniform_lowerFactorGaugedTraceBound_iff_targetCommutatorTraceBound
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    _ ↔ _ :=
      exists_uniform_targetCommutatorTraceBound_iff_obliqueShearBound
        owner lambda sourceBasis

end CCM24FiniteSGatePhysicalObliqueShearReduction
end CCM25Concrete
end Source
end ConnesWeilRH
