/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixFullKernelPairing

/-!
# Physical-kernel readout of the finite-S oblique shear

The square-zero shear of Proof 745 is the source inclusion followed by the
adjoint of the complete physical coframe leakage.  Its target response is
therefore one leakage/commutator matrix coefficient, rather than the centered
two-coframe difference of Proof 741.

This is an exact operator and diagonal-series reduction.  No family-uniform
bound, finite-S sign, Burnol identity, or RH conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalObliqueShearKernelReduction

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandJetOrientation
open CCM24FiniteSActualBandQuadraticCycle
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalSupport
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGatePhysicalObliqueShearReduction
open CCM24FiniteSGatePhysicalPrefixBoundaryKernelPairing
open CCM24FiniteSGatePhysicalPrefixFullKernelPairing
open CCM24FiniteSGatePhysicalPulledObliqueReduction
open CCM24FiniteSGatePhysicalTargetCommutatorReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorSignedKernelResponse
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem adjoint_sub_rectangular
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A B : H →L[ℂ] K) :
    (A - B)† = A† - B† := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]

/-- The pulled target projection is the source inclusion followed by the
adjoint metric coframe: `Q_S=J D_S†`. -/
theorem finiteEulerPulledTargetProjection_eq_inclusion_comp_metricCoframeAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledTargetProjection lambda family =
      sourceInclusion lambda ∘L (finiteEulerMetricCoframe lambda family)† := by
  rw [finiteEulerPulledTargetProjection_eq_sourceGramInvAmbient_comp_gram]
  apply ContinuousLinearMap.ext
  intro u
  simp only [finiteEulerSourceGramInvAmbient, finiteEulerMetricCoframe,
    finiteEulerAmbientGram, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    (finiteEulerGramInv_isSelfAdjoint lambda family).adjoint_eq,
    ContinuousLinearMap.comp_apply]

/-- The source Sonin projection annihilates the complete coframe leakage. -/
theorem sourceSoninProjection_comp_sourceSoninCoframeLeakage_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourceSoninCoframeLeakage lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hProjectionSq := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (finiteEulerMetricCoframe lambda family u))
    (show sourceSoninProjection lambda ∘L sourceSoninProjection lambda =
        sourceSoninProjection lambda by
      simpa only [ContinuousLinearMap.mul_def] using
        (sourceSoninProjection_isStarProjection lambda).isIdempotentElem)
  simp only [sourceSoninCoframeLeakage, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub,
    ContinuousLinearMap.zero_apply]
  simp only [ContinuousLinearMap.comp_apply] at hProjectionSq
  rw [hProjectionSq, sub_self]

/-- The same annihilation identity for the physical three-branch leakage. -/
theorem sourceSoninProjection_comp_sourcePhysicalCoframeLeakage_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninProjection lambda ∘L
        sourcePhysicalCoframeLeakage lambda family = 0 := by
  rw [← sourceSoninCoframeLeakage_eq_physical]
  exact sourceSoninProjection_comp_sourceSoninCoframeLeakage_eq_zero
    lambda family

/-- Adjoint orientation of the leakage annihilation: `L_S† R=0`. -/
theorem sourcePhysicalCoframeLeakage_adjoint_comp_sourceSoninProjection_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourcePhysicalCoframeLeakage lambda family)† ∘L
        sourceSoninProjection lambda = 0 := by
  have hZero :=
    (sourceSoninProjection_comp_sourcePhysicalCoframeLeakage_eq_zero
      lambda family)
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    have hZeroApply := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
        operator v)
      hZero
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hZeroApply
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.adjoint_inner_left,
      inner_zero_left]
    rw [← (sourceSoninProjection_isStarProjection lambda).isSelfAdjoint.adjoint_eq,
      ContinuousLinearMap.adjoint_inner_left, hZeroApply, inner_zero_right]

/-- The square-zero shear is exactly the source inclusion followed by the
adjoint source-Sonin leakage: `N_S=J L_S†`. -/
theorem finiteEulerPulledObliqueShear_eq_inclusion_comp_leakageAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledObliqueShear lambda family =
      sourceInclusion lambda ∘L
        (sourceSoninCoframeLeakage lambda family)† := by
  rw [finiteEulerPulledObliqueShear,
    finiteEulerPulledTargetProjection_eq_inclusion_comp_metricCoframeAdjoint,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion,
    adjoint_sub_rectangular]
  apply ContinuousLinearMap.ext
  intro u
  have hProjection := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier => operator u)
    (sourceInclusion_comp_adjoint lambda)
  simp only [ContinuousLinearMap.comp_apply] at hProjection
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hProjection]

/-- Physical version of `N_S=J L_S†`, with all three leakage branches kept
inside `L_S`. -/
theorem finiteEulerPulledObliqueShear_eq_inclusion_comp_physicalLeakageAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPulledObliqueShear lambda family =
      sourceInclusion lambda ∘L
        (sourcePhysicalCoframeLeakage lambda family)† := by
  rw [← sourceSoninCoframeLeakage_eq_physical]
  exact finiteEulerPulledObliqueShear_eq_inclusion_comp_leakageAdjoint
    lambda family

/-- The active target owner after deleting the redundant `J†J` pair. -/
noncomputable def finiteEulerPhysicalCoframeLeakageResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  (sourcePhysicalCoframeLeakage lambda family)† ∘L
    detectorOperator owner ∘L sourceInclusion lambda

/-- Proof 745's target response is one physical coframe-leakage response:
`Target_S=L_S† W J`. -/
theorem finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerTargetCommutatorResponse owner lambda family =
      finiteEulerPhysicalCoframeLeakageResponse owner lambda family := by
  rw [finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear]
  apply ContinuousLinearMap.ext
  intro u
  have hIsometry (v : sourceSoninCarrier lambda) :
      ((sourceInclusion lambda)†) (sourceInclusion lambda v) = v := by
    have h := congrArg
      (fun operator : sourceSoninCarrier lambda →L[ℂ]
        sourceSoninCarrier lambda => operator v)
      (sourceInclusion_adjoint_comp_self lambda)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  simp only [finiteEulerPulledObliqueShearResponse,
    finiteEulerPhysicalCoframeLeakageResponse,
    finiteEulerPulledObliqueShear_eq_inclusion_comp_physicalLeakageAdjoint,
    ContinuousLinearMap.comp_apply]
  rw [hIsometry]

/-- The leakage response sees only the fixed source commutator `[W,R]`.
The term containing `L_S† R` vanishes before any trace is taken. -/
theorem finiteEulerPhysicalCoframeLeakageResponse_eq_sourceBoundaryCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerPhysicalCoframeLeakageResponse owner lambda family =
      (sourcePhysicalCoframeLeakage lambda family)† ∘L
        sourceBoundaryCommutator owner lambda ∘L sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hSource := congrArg
    (fun operator : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      operator u)
    (sourceSoninProjection_comp_sourceInclusion_eq_self lambda)
  have hZero := congrArg
    (fun operator : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
      operator (detectorOperator owner (sourceInclusion lambda u)))
    (sourcePhysicalCoframeLeakage_adjoint_comp_sourceSoninProjection_eq_zero
      lambda family)
  simp only [ContinuousLinearMap.comp_apply] at hSource
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at hZero
  simp only [finiteEulerPhysicalCoframeLeakageResponse,
    sourceBoundaryCommutator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, map_sub]
  rw [hSource, hZero, sub_zero]

/-- A target diagonal is the negative of one complete physical pairing in the
single coframe orientation `(L_S x,Jx)`. -/
theorem inner_targetCommutatorResponse_eq_neg_physicalPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family x) =
      -sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourcePhysicalCoframeLeakage lambda family x)
        (sourceInclusion lambda x) := by
  rw [finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage,
    finiteEulerPhysicalCoframeLeakageResponse_eq_sourceBoundaryCommutator]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right,
    sourceBoundaryCommutator_eq_neg_threeBranch]
  simp only [ContinuousLinearMap.neg_apply, inner_neg_right]
  rw [sourceThreeBranchPhysicalPairing_eq_inner_threeBranchCommutator owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]

/-- The one complete scalar exposed by the oblique-shear reduction.  The
outer/reflected root, second support, and prolate terms remain in one bracket. -/
noncomputable def sourceObliqueShearPhysicalFullKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (x : sourceSoninCarrier lambda) : ℂ :=
  -(sourceTranslatedCompactRootSignedKernelPairing owner lambda a c
      (sourcePhysicalCoframeLeakage lambda family x) (sourceInclusion lambda x) +
    sourceSecondSupportProlateFullKernelPairing owner lambda a c
      (sourcePhysicalCoframeLeakage lambda family x) (sourceInclusion lambda x))

/-- The target diagonal is exactly the single full-kernel scalar. -/
theorem inner_targetCommutatorResponse_eq_obliqueShearFullKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : sourceSoninCarrier lambda) :
    inner ℂ x (finiteEulerTargetCommutatorResponse owner lambda family x) =
      sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c x := by
  rw [inner_targetCommutatorResponse_eq_neg_physicalPairing owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceThreeBranchPhysicalPairing_eq_signedKernel_add_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [inner_secondSupportProlateRemainderPairData_eq_fullKernelPairing owner
    lambda a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis hfactor]
  rfl

/-- The diagonal-series owner of the one full-kernel scalar. -/
noncomputable def finiteEulerObliqueShearFullKernelTrace
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) : ℂ :=
  ∑' i, sourceObliqueShearPhysicalFullKernelScalar owner lambda family a c
    (sourceBasis i)

/-- The ordinary target trace is the `tsum` of the single full-kernel scalar.
No trace cycle or rearrangement of the diagonal series is used. -/
theorem ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis := by
  rw [ordinaryTraceAlong, finiteEulerObliqueShearFullKernelTrace]
  apply tsum_congr
  intro i
  exact inner_targetCommutatorResponse_eq_obliqueShearFullKernelScalar owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor (sourceBasis i)

/-- Proof 745's one-shear response has the same full-kernel diagonal series. -/
theorem ordinaryTraceAlong_obliqueShearResponse_eq_fullKernelTrace
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerPulledObliqueShearResponse owner lambda family) =
      finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis := by
  rw [← finiteEulerTargetCommutatorResponse_eq_pulledObliqueShear]
  exact ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor

/-- Family-uniform target boundedness is exactly boundedness of the one
full-kernel diagonal series. -/
theorem exists_uniform_targetCommutatorTraceBound_iff_obliqueShearFullKernelBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis‖ ≤ bound) := by
  constructor
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, fun family => ?_⟩
    rw [← ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor]
    exact hbound family
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, fun family => ?_⟩
    rw [ordinaryTraceAlong_targetCommutator_eq_obliqueShearFullKernelTrace
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor]
    exact hbound family

/-- Proof 745's family-uniform one-shear target is equivalent to the one
full-kernel diagonal-series bound. -/
theorem exists_uniform_obliqueShearTraceBound_iff_fullKernelBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerPulledObliqueShearResponse owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis‖ ≤ bound) := by
  constructor
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, fun family => ?_⟩
    rw [← ordinaryTraceAlong_obliqueShearResponse_eq_fullKernelTrace owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor]
    exact hbound family
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, fun family => ?_⟩
    rw [ordinaryTraceAlong_obliqueShearResponse_eq_fullKernelTrace owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor]
    exact hbound family

/-- The route-facing Gate quantifiers now land on the single physical
full-kernel scalar.  This theorem transfers Proof 745's exact equivalence; it
does not supply the bound on the right. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_obliqueShearFullKernelBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
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
      ‖finiteEulerObliqueShearFullKernelTrace owner lambda family a c
        sourceBasis‖ ≤ bound) := by
  calc
    _ ↔ ∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
        ‖ordinaryTraceAlong sourceBasis
          (finiteEulerPulledObliqueShearResponse
            owner lambda family)‖ ≤ bound :=
      exists_uniform_lowerFactorGaugedTraceBound_iff_obliqueShearBound
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    _ ↔ _ :=
      exists_uniform_obliqueShearTraceBound_iff_fullKernelBound owner lambda
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor

end CCM24FiniteSGatePhysicalObliqueShearKernelReduction
end CCM25Concrete
end Source
end ConnesWeilRH
