/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorPrimitiveKernel

/-!
# Signed compact-kernel response

Proof 472's four primitive outer/reflected terms are recombined before any
estimate.  The common negative and positive compact-root legs determine one
signed operator `P^dagger N - N^dagger P`; the four terms are the two-sided
response of this same operator to the source prefix.  The operator is then
identified with the existing genuine half-line boundary commutator.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorSignedKernelResponse

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedDetectorTrace
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorPrimitiveKernel

/-- The basis-free signed compact-root operator shared by all four primitive
outer/reflected terms. -/
noncomputable def sourceCompactRootSignedKernelOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (a c : ℝ) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (positiveBoundaryRootFactor owner.sourceTest a c)† ∘L
      negativeBoundaryRootFactor owner.sourceTest a c -
    (negativeBoundaryRootFactor owner.sourceTest a c)† ∘L
      positiveBoundaryRootFactor owner.sourceTest a c

/-- The four-term outer/reflected scalar after both orientations have been
combined into the one signed compact-kernel operator. -/
noncomputable def sourceTranslatedCompactRootSignedKernelPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (x y : finiteSCarrier) : ℂ :=
  let translation := (cc20GlobalLogTranslation
    (Real.log lambda)).toContinuousLinearMap
  let prefixAdjoint := (radialSupportProjection lambda ∘L
    sourceFourierSupportProjection lambda).adjoint
  let signedKernel := sourceCompactRootSignedKernelOperator owner a c
  inner ℂ (translation (prefixAdjoint x))
      (signedKernel (translation y)) +
    inner ℂ (translation x)
      (signedKernel (translation (prefixAdjoint y)))

/-- The four primitive kernel terms are exactly the two-sided response of one
signed compact-kernel operator.  This is an algebraic recombination before
any absolute value, trace split, or branchwise estimate. -/
theorem sourceTranslatedCompactRootKernelOuterReflectedPairing_eq_signedKernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (x y : finiteSCarrier) :
    sourceTranslatedCompactRootKernelOuterReflectedPairing owner lambda
        a c x y =
      sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y := by
  unfold sourceTranslatedCompactRootKernelOuterReflectedPairing
    sourceTranslatedCompactRootSignedKernelPairing
  unfold sourceCompactRootSignedKernelOperator
  unfold translatedNegativeBoundaryKernelLeg
    translatedPositiveBoundaryKernelLeg
    negativeBoundaryRootFactor
    positiveBoundaryRootFactor
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

/-- The basis-free signed kernel operator is the existing signed compact-pair
owner.  The Hilbert bases certify trace legality but do not change the
operator. -/
theorem sourceCompactRootSignedKernelOperator_eq_signedBoundaryOperator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    sourceCompactRootSignedKernelOperator owner a c =
      signedBoundaryOperator owner.sourceTest a c negativeBasis positiveBasis
        outputBasis globalBasis := by
  rw [signedBoundaryOperator_eq_adjoint_sub]
  rw [pairData_traceProduct_eq]
  unfold sourceCompactRootSignedKernelOperator
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- Hence the signed kernel operator is not a new model: it is the genuine
commutator of the positive half-line projection with the compact-window
detector. -/
theorem sourceCompactRootSignedKernelOperator_eq_boundaryCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    sourceCompactRootSignedKernelOperator owner a c =
      cc20Commutator cc20PositiveHalfLineProjection
        (windowedBoundaryDetector owner.sourceTest a c) := by
  rw [sourceCompactRootSignedKernelOperator_eq_signedBoundaryOperator owner
    a c negativeBasis positiveBasis outputBasis globalBasis]
  exact signedBoundaryOperator_eq_commutator owner.sourceTest a c hac
    negativeBasis positiveBasis outputBasis globalBasis

/-- The signed kernel operator inherits the named-basis trace-class witness
from the genuine compact-root pair. -/
theorem sourceCompactRootSignedKernelOperator_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    PositiveTrace.IsTraceClassAlong globalBasis
      (sourceCompactRootSignedKernelOperator owner a c) := by
  rw [sourceCompactRootSignedKernelOperator_eq_signedBoundaryOperator owner
    a c negativeBasis positiveBasis outputBasis globalBasis]
  exact signedBoundaryOperator_isTraceClassAlong owner.sourceTest a c
    negativeBasis positiveBasis outputBasis globalBasis

/-- The shared signed kernel is skew-adjoint, so its response retains the
exact antisymmetry of the two compact-root orientations. -/
theorem sourceCompactRootSignedKernelOperator_adjoint_eq_neg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (sourceCompactRootSignedKernelOperator owner a c).adjoint =
      -sourceCompactRootSignedKernelOperator owner a c := by
  rw [sourceCompactRootSignedKernelOperator_eq_boundaryCommutator owner a c hac
    negativeBasis positiveBasis outputBasis globalBasis]
  exact cc20Commutator_adjoint_eq_neg _ _
    cc20PositiveHalfLineProjection_isSelfAdjoint
    (windowedBoundaryDetector_isSelfAdjoint owner.sourceTest a c)

/-- The complete physical scalar is the one signed-kernel response plus the
still-coupled second-support/prolate remainder. -/
theorem sourceThreeBranchPhysicalPairing_eq_signedKernel_add_remainder
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
      sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y +
        inner ℂ
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).left x)
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).right y) := by
  rw [sourceThreeBranchPhysicalPairing_eq_kernel_add_remainder owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceTranslatedCompactRootKernelOuterReflectedPairing_eq_signedKernel]

/-- The completed displacement diagonal with the primitive four terms
recombined into the single signed compact-kernel response. -/
noncomputable def rootCompletedDetectorTranslationSignedKernelDiagonal
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
  (-1 : ℂ) *
    (sourceTranslatedCompactRootSignedKernelPairing owner lambda a c x y +
      inner ℂ
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor).left x)
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor).right y))

/-- The displacement atom trace is one global-basis `tsum` of the signed
compact-kernel response and the unchanged coupled remainder. -/
theorem rootCompletedDetectorSoninTranslationTrace_eq_signedKernel_tsum
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
      ∑' index, rootCompletedDetectorTranslationSignedKernelDiagonal owner
        lambda displacement a c hac hsupp reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor index := by
  rw [rootCompletedDetectorSoninTranslationTrace_eq_primitiveKernel_tsum
    owner lambda displacement a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor]
  apply tsum_congr
  intro index
  unfold rootCompletedDetectorTranslationPrimitiveKernelDiagonal
    rootCompletedDetectorTranslationSignedKernelDiagonal
  dsimp only
  rw [sourceTranslatedCompactRootKernelOuterReflectedPairing_eq_signedKernel]

end CCM24FiniteSRootCompletedDetectorSignedKernelResponse
end CCM25Concrete
end Source
end ConnesWeilRH
