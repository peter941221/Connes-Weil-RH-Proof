/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorSignedKernelResponse

/-!
# One completed compact-kernel boundary operator

The two-sided signed-kernel response from Proof 473 and the coupled
second-support/prolate remainder are assembled into one operator on the
original finite-S carrier.  This explicit operator is then identified with
the trace product of the existing complete three-branch Hilbert--Schmidt pair.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorCompletedKernelOperator

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedDetectorTrace
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorSignedKernelResponse

/-- A generic two-sided response is one matrix coefficient of the sum of its
two operator orderings. -/
theorem twoSidedAdjointResponse_eq_inner_addOperator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (translation prefixOperator signed : H →L[ℂ] H) (x y : H) :
    inner ℂ (translation (prefixOperator.adjoint x))
          (signed (translation y)) +
        inner ℂ (translation x)
          (signed (translation (prefixOperator.adjoint y))) =
      inner ℂ x
        (((prefixOperator ∘L translation.adjoint ∘L signed ∘L translation) +
          (translation.adjoint ∘L signed ∘L translation ∘L
            prefixOperator.adjoint)) y) := by
  calc
    inner ℂ (translation (prefixOperator.adjoint x))
          (signed (translation y)) +
        inner ℂ (translation x)
          (signed (translation (prefixOperator.adjoint y))) =
      inner ℂ (prefixOperator.adjoint x)
          (translation.adjoint (signed (translation y))) +
        inner ℂ x
          (translation.adjoint
            (signed (translation (prefixOperator.adjoint y)))) := by
        rw [translation.adjoint_inner_right,
          translation.adjoint_inner_right]
    _ = inner ℂ x
          (prefixOperator (translation.adjoint (signed (translation y)))) +
        inner ℂ x
          (translation.adjoint
            (signed (translation (prefixOperator.adjoint y)))) := by
        rw [prefixOperator.adjoint_inner_left]
    _ = inner ℂ x
        (((prefixOperator ∘L translation.adjoint ∘L signed ∘L translation) +
          (translation.adjoint ∘L signed ∘L translation ∘L
            prefixOperator.adjoint)) y) := by
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.add_apply, inner_add_right]

/-- The signed outer/reflected contribution as one operator on the original
finite-S carrier. -/
noncomputable def sourceTranslatedSignedKernelPrefixOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  let translation := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  let prefixOperator := radialSupportProjection lambda ∘L
    sourceFourierSupportProjection lambda
  let signed := sourceCompactRootSignedKernelOperator owner a c
  (prefixOperator ∘L translation.adjoint ∘L signed ∘L translation) +
    (translation.adjoint ∘L signed ∘L translation ∘L
      prefixOperator.adjoint)

/-- Proof 473's two signed response terms are one matrix coefficient of the
explicit prefix/signed-kernel operator. -/
theorem sourceTranslatedCompactRootSignedKernelPairing_eq_inner_prefixOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (x y : finiteSCarrier) :
    sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y =
      inner ℂ x
        (sourceTranslatedSignedKernelPrefixOperator owner lambda a c y) := by
  unfold sourceTranslatedCompactRootSignedKernelPairing
    sourceTranslatedSignedKernelPrefixOperator
  dsimp only
  exact twoSidedAdjointResponse_eq_inner_addOperator _ _ _ x y

/-- The complete explicit boundary operator: one signed compact-root prefix
response plus the still-unsplit second-support/prolate trace product. -/
noncomputable def sourceCompletedSignedKernelBoundaryOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ιr κr τr ν : Type*}
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  sourceTranslatedSignedKernelPrefixOperator owner lambda a c +
    (secondSupportProlateRemainderPairData owner lambda a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor).traceProduct

/-- The complete physical scalar is one matrix coefficient of the explicit
completed operator. -/
theorem sourceThreeBranchPhysicalPairing_eq_inner_completedKernelOperator
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x y : finiteSCarrier) :
    sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor x y =
      inner ℂ x
        (sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac
          hsupp reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis hfactor y) := by
  rw [sourceThreeBranchPhysicalPairing_eq_signedKernel_add_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceTranslatedCompactRootSignedKernelPairing_eq_inner_prefixOperator]
  unfold sourceCompletedSignedKernelBoundaryOperator
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  rw [BasisHilbertSchmidtPairData.traceProduct,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- The explicit completed operator is exactly the trace product of the
existing genuine complete three-branch Hilbert--Schmidt pair. -/
theorem sourceThreeBranchPairData_traceProduct_eq_completedKernelOperator
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
    (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor).traceProduct =
      sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [BasisHilbertSchmidtPairData.traceProduct,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rw [sourceThreeBranchPairData_inner_eq_physicalPairing owner lambda a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  exact sourceThreeBranchPhysicalPairing_eq_inner_completedKernelOperator owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor x y

/-- The explicit completed operator inherits trace legality from that same
three-branch pair, without estimating its summands separately. -/
theorem sourceCompletedSignedKernelBoundaryOperator_isTraceClassAlong
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
    PositiveTrace.IsTraceClassAlong globalBasis
      (sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor) := by
  rw [← sourceThreeBranchPairData_traceProduct_eq_completedKernelOperator owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  exact (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis hfactor).traceProduct_isTraceClassAlong

/-- The completed displacement diagonal as one matrix coefficient of the
single explicit completed operator. -/
noncomputable def rootCompletedDetectorTranslationCompletedKernelDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ιr κr τr ν : Type*}
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (index : ν) : ℂ :=
  let x := sourceBandProjection lambda (globalBasis index)
  let y := (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap x
  (-1 : ℂ) * inner ℂ x
    (sourceCompletedSignedKernelBoundaryOperator owner lambda a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor y)

/-- The atom trace is one `tsum` of matrix coefficients of the single
completed trace-class boundary operator. -/
theorem rootCompletedDetectorSoninTranslationTrace_eq_completedKernel_tsum
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
        rootCompletedDetectorTranslationCompletedKernelDiagonal owner lambda
          displacement a c hac hsupp reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
          index := by
  rw [rootCompletedDetectorSoninTranslationTrace_eq_physicalDiagonal_tsum
    owner lambda displacement a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor]
  apply tsum_congr
  intro index
  unfold rootCompletedDetectorTranslationPhysicalDiagonal
    rootCompletedDetectorTranslationCompletedKernelDiagonal
  rw [sourceThreeBranchPhysicalPairing_eq_inner_completedKernelOperator owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  simp only [neg_one_mul]

end CCM24FiniteSRootCompletedDetectorCompletedKernelOperator
end CCM25Concrete
end Source
end ConnesWeilRH
