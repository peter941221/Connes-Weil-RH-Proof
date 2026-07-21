/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorPrimitiveOuter

/-!
# Primitive compact-root kernel pairing

The abstract primitive pair exposed by Proof 471 is unfolded to the actual
continuous-kernel operators on the compact negative and positive input
windows.  The four outer/reflected terms remain one antisymmetrized scalar,
and the second-support/prolate remainder remains coupled.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorPrimitiveKernel

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open SelectedCrossingKernel
open SelectedCrossingOperatorBridge
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSRootCompletedDetectorTrace
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
open CCM24FiniteSRootCompletedDetectorPrimitiveOuter

/-- The translated negative boundary leg written directly as its continuous
kernel operator after compact-window restriction. -/
noncomputable def translatedNegativeBoundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  CC20Concrete.ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (BoundaryNegativeInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (negativeBoundaryRootKernel owner.sourceTest a c) ∘L
    globalL2ToKernelInterval (a - c) 0 0 ∘L
    (cc20GlobalLogTranslation
      (Real.log lambda)).toContinuousLinearMap

/-- The translated positive boundary leg written directly as its continuous
kernel operator after compact-window restriction. -/
noncomputable def translatedPositiveBoundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) :
    finiteSCarrier →L[ℂ]
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) :=
  CC20Concrete.ContinuousKernelHilbertSchmidt.operator
      (volume : Measure (BoundaryPositiveInputInterval a c))
      (volume : Measure (BoundaryOutputInterval a c))
      (positiveBoundaryRootKernel owner.sourceTest a c) ∘L
    globalL2ToKernelInterval 0 (c - a) 0 ∘L
    (cc20GlobalLogTranslation
      (Real.log lambda)).toContinuousLinearMap

/-- The left leg of the translated primitive pair is the actual negative
compact-window continuous-kernel operator. -/
theorem translatedCompactRootPairData_left_eq_boundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left =
      translatedNegativeBoundaryKernelLeg owner lambda a c := by
  calc
    _ = negativeBoundaryRootFactor owner.sourceTest a c ∘L
        (cc20GlobalLogTranslation
          (-Real.log lambda)).toContinuousLinearMap.adjoint := rfl
    _ = negativeBoundaryRootFactor owner.sourceTest a c ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := by
      rw [SelectedCrossingOperatorBridge.cc20GlobalLogTranslation_neg_adjoint]
    _ = translatedNegativeBoundaryKernelLeg owner lambda a c := rfl

/-- The right leg of the translated primitive pair is the actual positive
compact-window continuous-kernel operator. -/
theorem translatedCompactRootPairData_right_eq_boundaryKernelLeg
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right =
      translatedPositiveBoundaryKernelLeg owner lambda a c := by
  calc
    _ = positiveBoundaryRootFactor owner.sourceTest a c ∘L
        (cc20GlobalLogTranslation
          (Real.log lambda)).toContinuousLinearMap := rfl
    _ = translatedPositiveBoundaryKernelLeg owner lambda a c := rfl

/-- Proof 471's four-term antisymmetrization, now stated entirely through the
two concrete compact `Lp` continuous-kernel legs. -/
noncomputable def sourceTranslatedCompactRootKernelOuterReflectedPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (x y : finiteSCarrier) : ℂ :=
  let negativeLeg := translatedNegativeBoundaryKernelLeg owner lambda a c
  let positiveLeg := translatedPositiveBoundaryKernelLeg owner lambda a c
  let prefixOperator := radialSupportProjection lambda ∘L
    sourceFourierSupportProjection lambda
  (inner ℂ (positiveLeg (prefixOperator.adjoint x)) (negativeLeg y) -
      inner ℂ (negativeLeg (prefixOperator.adjoint x)) (positiveLeg y)) -
    (inner ℂ (negativeLeg x) (positiveLeg (prefixOperator.adjoint y)) -
      inner ℂ (positiveLeg x) (negativeLeg (prefixOperator.adjoint y)))

/-- The primitive pair scalar is exactly its concrete compact-kernel scalar.
No pointwise representative or Schwartz-core assumption is inserted. -/
theorem sourceTranslatedCompactRootOuterReflectedPairing_eq_kernel
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (x y : finiteSCarrier) :
    sourceTranslatedCompactRootOuterReflectedPairing owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis x y =
      sourceTranslatedCompactRootKernelOuterReflectedPairing owner lambda
        a c x y := by
  unfold sourceTranslatedCompactRootOuterReflectedPairing
    sourceTranslatedCompactRootKernelOuterReflectedPairing
  dsimp only
  rw [translatedCompactRootPairData_left_eq_boundaryKernelLeg owner lambda
    a c negativeBasis positiveBasis outputBasis globalBasis]
  rw [translatedCompactRootPairData_right_eq_boundaryKernelLeg owner lambda
    a c negativeBasis positiveBasis outputBasis globalBasis]

/-- The complete physical scalar uses the concrete kernel bracket while the
second-support/prolate coordinate remains one unsplit remainder. -/
theorem sourceThreeBranchPhysicalPairing_eq_kernel_add_remainder
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
      sourceTranslatedCompactRootKernelOuterReflectedPairing owner lambda
          a c x y +
        inner ℂ
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).left x)
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).right y) := by
  rw [sourceThreeBranchPhysicalPairing_eq_primitiveOuter_add_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  rw [sourceTranslatedCompactRootOuterReflectedPairing_eq_kernel owner lambda
    a c negativeBasis positiveBasis outputBasis globalBasis]

/-- The completed displacement diagonal with the concrete kernel bracket
visible and the coupled remainder unchanged. -/
noncomputable def rootCompletedDetectorTranslationPrimitiveKernelDiagonal
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
    (sourceTranslatedCompactRootKernelOuterReflectedPairing owner lambda a c
        x y +
      inner ℂ
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor).left x)
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor).right y))

/-- The atom trace is one global-basis `tsum` of the concrete primitive
kernel bracket plus the still-coupled remainder. -/
theorem rootCompletedDetectorSoninTranslationTrace_eq_primitiveKernel_tsum
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
      ∑' index, rootCompletedDetectorTranslationPrimitiveKernelDiagonal owner
        lambda displacement a c hac hsupp reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor index := by
  rw [rootCompletedDetectorSoninTranslationTrace_eq_primitiveDiagonal_tsum
    owner lambda displacement a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor]
  apply tsum_congr
  intro index
  unfold rootCompletedDetectorTranslationPrimitiveDiagonal
    rootCompletedDetectorTranslationPrimitiveKernelDiagonal
  dsimp only
  rw [sourceTranslatedCompactRootOuterReflectedPairing_eq_kernel owner lambda
    a c negativeBasis positiveBasis outputBasis globalBasis]

end CCM24FiniteSRootCompletedDetectorPrimitiveKernel
end CCM25Concrete
end Source
end ConnesWeilRH
