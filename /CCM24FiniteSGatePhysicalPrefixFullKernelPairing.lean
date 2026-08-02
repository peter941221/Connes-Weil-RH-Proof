/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalPrefixBoundaryKernelPairing

/-!
# Full compact-kernel pairing for the centered physical Gate prefix

Proof 740 exposes the outer/reflected compact-root signed kernel while keeping
the second-support/prolate pair coupled.  This file opens that coupled pair to
the reflected compact-root kernel legs and the genuine source prolate square
root.  All five signed terms remain inside one scalar before the two centered
coframe orientations are subtracted.

No termwise norm, cutoff commutation, uniform estimate, finite-S sign, Burnol
identity, or RH premise is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalPrefixFullKernelPairing

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGatePhysicalPrefixBoundaryCenteredCycle
open CCM24FiniteSGatePhysicalPrefixBoundaryKernelPairing
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalCancellationEndpointNormalForm
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24FiniteSRawRemainderCommonPair
open CCM24RadialBoundaryPairTransport
open CCM24ReflectedCompactRoot
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorPrimitiveOuter

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The reflected compact root's translated negative continuous-kernel leg. -/
noncomputable def reflectedTranslatedNegativeBoundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) :=
  negativeBoundaryRootFactor owner.sourceTest.reflection (-c) (-a) ∘L
    (cc20GlobalLogTranslation
      (Real.log lambda)).toContinuousLinearMap

/-- The reflected compact root's translated positive continuous-kernel leg. -/
noncomputable def reflectedTranslatedPositiveBoundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) :=
  positiveBoundaryRootFactor owner.sourceTest.reflection (-c) (-a) ∘L
    (cc20GlobalLogTranslation
      (Real.log lambda)).toContinuousLinearMap

/-- The reflected translated pair's left leg is its actual negative compact
continuous-kernel operator. -/
theorem reflectedTranslatedCompactRootPairData_left_eq_kernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left =
      reflectedTranslatedNegativeBoundaryKernelLeg owner lambda a c := by
  calc
    _ = negativeBoundaryRootFactor owner.sourceTest.reflection (-c) (-a) ∘L
        (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap.adjoint := rfl
    _ = negativeBoundaryRootFactor owner.sourceTest.reflection (-c) (-a) ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
      rw [SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint]
    _ = reflectedTranslatedNegativeBoundaryKernelLeg owner lambda a c := rfl

/-- The reflected translated pair's right leg is its actual positive compact
continuous-kernel operator. -/
theorem reflectedTranslatedCompactRootPairData_right_eq_kernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right =
      reflectedTranslatedPositiveBoundaryKernelLeg owner lambda a c := by
  rfl

/-- The negative reflected root leg after the genuine Hardy--Titchmarsh
second-support transport. -/
noncomputable def sourceSecondSupportNegativeBoundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) :=
  reflectedTranslatedNegativeBoundaryKernelLeg owner lambda a c ∘L
    archimedeanHardyTitchmarshOperator

/-- The positive reflected root leg after the genuine Hardy--Titchmarsh
second-support transport. -/
noncomputable def sourceSecondSupportPositiveBoundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) :=
  reflectedTranslatedPositiveBoundaryKernelLeg owner lambda a c ∘L
    archimedeanHardyTitchmarshOperator

/-- The actual second-support pair's left leg is the reflected negative kernel
after Hardy--Titchmarsh transport. -/
theorem sourceSecondSupportCompactRootPairData_left_eq_kernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (sourceSecondSupportCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left =
      sourceSecondSupportNegativeBoundaryKernelLeg owner lambda a c := by
  calc
    _ = (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left ∘L
        archimedeanHardyTitchmarshOperator.adjoint := rfl
    _ = reflectedTranslatedNegativeBoundaryKernelLeg owner lambda a c ∘L
        archimedeanHardyTitchmarshOperator.adjoint := by
      rw [reflectedTranslatedCompactRootPairData_left_eq_kernelLeg]
    _ = reflectedTranslatedNegativeBoundaryKernelLeg owner lambda a c ∘L
        archimedeanHardyTitchmarshOperator := by
      rw [archimedeanHardyTitchmarshOperator_isSelfAdjoint.adjoint_eq]
    _ = sourceSecondSupportNegativeBoundaryKernelLeg owner lambda a c := rfl

/-- The actual second-support pair's right leg is the reflected positive
kernel after Hardy--Titchmarsh transport. -/
theorem sourceSecondSupportCompactRootPairData_right_eq_kernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (sourceSecondSupportCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right =
      sourceSecondSupportPositiveBoundaryKernelLeg owner lambda a c := by
  calc
    _ = (reflectedTranslatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right ∘L
        archimedeanHardyTitchmarshOperator := rfl
    _ = reflectedTranslatedPositiveBoundaryKernelLeg owner lambda a c ∘L
        archimedeanHardyTitchmarshOperator := by
      rw [reflectedTranslatedCompactRootPairData_right_eq_kernelLeg]
    _ = sourceSecondSupportPositiveBoundaryKernelLeg owner lambda a c := rfl

/-- The coupled second-support/prolate scalar with all primitive factors
visible.  It remains one signed object. -/
noncomputable def sourceSecondSupportProlateFullKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (x y : finiteSCarrier) : ℂ :=
  let R := radialSupportProjection lambda
  let negativeLeg :=
    sourceSecondSupportNegativeBoundaryKernelLeg owner lambda a c
  let positiveLeg :=
    sourceSecondSupportPositiveBoundaryKernelLeg owner lambda a c
  let prolate := sourceProlateHilbertSchmidtFactor lambda
  let detector := detectorOperator owner
  (inner ℂ (positiveLeg (R x)) (negativeLeg (R y)) -
      inner ℂ (negativeLeg (R x)) (positiveLeg (R y))) -
    (inner ℂ (prolate x) (prolate (detector y)) -
      inner ℂ (prolate (detector x)) (prolate y))

/-- The old coupled pair coefficient is exactly the full reflected-root and
prolate signed kernel scalar. -/
theorem inner_secondSupportProlateRemainderPairData_eq_fullKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x y : finiteSCarrier) :
    inner ℂ
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis globalBasis hfactor).left x)
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          negativeBasis positiveBasis outputBasis globalBasis hfactor).right y) =
      sourceSecondSupportProlateFullKernelPairing owner lambda a c x y := by
  let secondBase := sourceSecondSupportCompactRootPairData owner lambda a c
    negativeBasis positiveBasis outputBasis globalBasis
  let second := secondSupportCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let forward := prolateForwardPairData owner lambda globalBasis hfactor
  let reverse := prolateReversePairData owner lambda globalBasis hfactor
  let prolate := prolateCommutatorPairData' owner lambda globalBasis hfactor
  have hsecond : inner ℂ (second.left x) (second.right y) =
      inner ℂ
          (sourceSecondSupportPositiveBoundaryKernelLeg owner lambda a c
            (radialSupportProjection lambda x))
          (sourceSecondSupportNegativeBoundaryKernelLeg owner lambda a c
            (radialSupportProjection lambda y)) -
        inner ℂ
          (sourceSecondSupportNegativeBoundaryKernelLeg owner lambda a c
            (radialSupportProjection lambda x))
          (sourceSecondSupportPositiveBoundaryKernelLeg owner lambda a c
            (radialSupportProjection lambda y)) := by
    dsimp only [second]
    rw [secondSupportCommutatorPairData,
      boundedAdjointSub_inner_pairing_eq_sub]
    rw [(radialSupportProjection_isStarProjection lambda)
      |>.isSelfAdjoint.adjoint_eq]
    dsimp only [secondBase]
    rw [sourceSecondSupportCompactRootPairData_left_eq_kernelLeg,
      sourceSecondSupportCompactRootPairData_right_eq_kernelLeg]
  have hprolate : inner ℂ (prolate.left x) (prolate.right y) =
      inner ℂ (sourceProlateHilbertSchmidtFactor lambda x)
          (sourceProlateHilbertSchmidtFactor lambda
            (detectorOperator owner y)) -
        inner ℂ
          (sourceProlateHilbertSchmidtFactor lambda
            (detectorOperator owner x))
          (sourceProlateHilbertSchmidtFactor lambda y) := by
    dsimp only [prolate]
    rw [prolateCommutatorPairData', l2Sum_inner_pairing_eq_add]
    simp only [BasisHilbertSchmidtPairData.smulRight,
      ContinuousLinearMap.neg_apply, neg_one_smul, inner_neg_right]
    dsimp only [forward, reverse, prolateForwardPairData,
      prolateReversePairData, BasisHilbertSchmidtPairData.boundedSandwich,
      sourceProlatePairData]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
      (detectorOperator_isSelfAdjoint owner).adjoint_eq]
  rw [secondSupportProlateRemainderPairData,
    l2Sum_inner_pairing_eq_add]
  simp only [BasisHilbertSchmidtPairData.smulRight,
    ContinuousLinearMap.neg_apply, neg_one_smul, inner_neg_right]
  change inner ℂ (second.left x) (second.right y) -
      inner ℂ (prolate.left x) (prolate.right y) = _
  rw [hsecond, hprolate]
  rfl

/-- One full centered Gate scalar: outer/reflected root, second-support
reflected root, and prolate correction all remain in one signed bracket. -/
noncomputable def sourceGatePhysicalFullKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (x : sourceSoninCarrier lambda) : ℂ :=
  let Jx := sourceInclusion lambda x
  let Ux := sourceEndpointCancellationResidual lambda family x
  let Fx := sourceActualBandForwardCoframe lambda family x
  (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Jx Ux +
      sourceSecondSupportProlateFullKernelPairing owner lambda a c Jx Ux) -
    (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c Fx Jx +
      sourceSecondSupportProlateFullKernelPairing owner lambda a c Fx Jx)

/-- Proof 740's centered kernel scalar is exactly the full primitive kernel
scalar. -/
theorem sourceGatePhysicalCenteredKernelScalar_eq_fullKernelScalar
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : sourceSoninCarrier lambda) :
    sourceGatePhysicalCenteredKernelScalar owner lambda family a c hac hsupp
        negativeBasis positiveBasis outputBasis globalBasis hfactor x =
      sourceGatePhysicalFullKernelScalar owner lambda family a c x := by
  rw [sourceGatePhysicalCenteredKernelScalar]
  rw [inner_secondSupportProlateRemainderPairData_eq_fullKernelPairing owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
    hfactor]
  rw [inner_secondSupportProlateRemainderPairData_eq_fullKernelPairing owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
    hfactor]
  rfl

/-- The ordered finite prefix of the full physical kernel scalar. -/
noncomputable def sourceGatePhysicalPrefixFullKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    sourceGatePhysicalFullKernelScalar owner lambda family a c (sourceBasis i)

/-- Proof 740's finite kernel pairing is the full primitive kernel prefix. -/
theorem sourceGatePhysicalPrefixCenteredKernelPairing_eq_fullKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (N : ℕ) :
    sourceGatePhysicalPrefixCenteredKernelPairing owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis globalBasis sourceBasis
        hfactor N =
      sourceGatePhysicalPrefixFullKernelPairing owner lambda family a c
        sourceBasis N := by
  rw [sourceGatePhysicalPrefixCenteredKernelPairing,
    sourceGatePhysicalPrefixFullKernelPairing]
  apply Finset.sum_congr rfl
  intro i _
  exact sourceGatePhysicalCenteredKernelScalar_eq_fullKernelScalar owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    globalBasis hfactor (sourceBasis i)

/-- Proof 739's centered boundary trace is the same full primitive kernel
prefix. -/
theorem ordinaryTraceAlong_prefixBoundaryCenteredResponse_eq_fullKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (N : ℕ) :
    ordinaryTraceAlong boundaryBasis
        (sourceGatePhysicalPrefixBoundaryCenteredResponse owner lambda family
          a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis N hfactor) =
      sourceGatePhysicalPrefixFullKernelPairing owner lambda family a c
        sourceBasis N := by
  rw [ordinaryTraceAlong_prefixBoundaryCenteredResponse_eq_kernelPairing owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor N]
  exact sourceGatePhysicalPrefixCenteredKernelPairing_eq_fullKernelPairing owner
    lambda family a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis sourceBasis hfactor N

/-- A uniform bound on the one full primitive kernel prefix feeds the exact
ordered Gate consumer. -/
theorem lowerFactorGaugedResponse_trace_norm_le_of_prefixFullKernelBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ℕ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hbound : ∀ N : ℕ,
      ‖sourceGatePhysicalPrefixFullKernelPairing owner lambda family a c
        sourceBasis N‖ ≤ bound) :
    ‖ordinaryTraceAlong sourceBasis
      (lowerFactorGaugedActualBandCompletedRelativeResponse
        owner lambda family)‖ ≤ bound := by
  apply lowerFactorGaugedResponse_trace_norm_le_of_prefixCenteredKernelBound
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound
  intro N
  rw [sourceGatePhysicalPrefixCenteredKernelPairing_eq_fullKernelPairing owner
    lambda family a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis sourceBasis hfactor N]
  exact hbound N

end CCM24FiniteSGatePhysicalPrefixFullKernelPairing
end CCM25Concrete
end Source
end ConnesWeilRH
