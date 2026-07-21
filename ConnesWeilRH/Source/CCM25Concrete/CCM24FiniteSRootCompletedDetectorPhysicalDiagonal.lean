/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorBoundaryTrace

/-!
# Complete physical diagonal for one detector displacement

The boundary pairing from Proof 469 is expanded only through the two nested
`L2` sums of the complete physical owner.  The second-support and prolate
coordinates remain coupled, and no absolute value is taken.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorPhysicalDiagonal

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedDetectorCommutator
open CCM24FiniteSRootCompletedDetectorTrace

/-- The inner product of an `L2`-sum pair is the signed-preserving sum of the
two coordinate pairings. -/
theorem l2Sum_inner_pairing_eq_add
    {H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {basis : HilbertBasis ι ℂ H}
    (first : BasisHilbertSchmidtPairData (G := G) basis)
    (second : BasisHilbertSchmidtPairData (G := K) basis)
    (x y : H) :
    inner ℂ
        ((BasisHilbertSchmidtPairData.l2Sum first second).left x)
        ((BasisHilbertSchmidtPairData.l2Sum first second).right y) =
      inner ℂ (first.left x) (first.right y) +
        inner ℂ (second.left x) (second.right y) := by
  unfold BasisHilbertSchmidtPairData.l2Sum
  simp [ContinuousLinearMap.comp_apply, WithLp.prod_inner_apply]

/-- The complete fixed-source boundary pairing, expanded only into the outer,
reflected-outer, and coupled second-support/prolate coordinates. -/
noncomputable def sourceThreeBranchPhysicalPairing
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
    (leftInput rightInput : finiteSCarrier) : ℂ :=
  let outer := outerCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let reflected := reflectedOuterCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let remainder := secondSupportProlateRemainderPairData owner lambda a c hac
    hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  inner ℂ (outer.left leftInput) (outer.right rightInput) +
    inner ℂ (reflected.left leftInput) (reflected.right rightInput) +
    inner ℂ (remainder.left leftInput) (remainder.right rightInput)

/-- The single inner product of the complete physical pair is exactly the
three-coordinate physical pairing, before any absolute value. -/
theorem sourceThreeBranchPairData_inner_eq_physicalPairing
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
    (leftInput rightInput : finiteSCarrier) :
    inner ℂ
        ((sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).left
            leftInput)
        ((sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
          positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
            rightInput) =
      sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        leftInput rightInput := by
  rw [sourceThreeBranchPairData]
  rw [l2Sum_inner_pairing_eq_add, l2Sum_inner_pairing_eq_add]
  rfl

/-- The complete signed physical diagonal at one global basis vector and one
causal displacement. -/
noncomputable def rootCompletedDetectorTranslationPhysicalDiagonal
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
    (index : ν) : ℂ :=
  -sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis hfactor
    (sourceBandProjection lambda (globalBasis index))
    ((cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap
      (sourceBandProjection lambda (globalBasis index)))

/-- The ordinary trace of one displacement atom is the sum of the complete
signed physical diagonal.  The second-support/prolate cancellation remains
inside every summand. -/
theorem rootCompletedDetectorSoninTranslationTrace_eq_physicalDiagonal_tsum
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
      ∑' index, rootCompletedDetectorTranslationPhysicalDiagonal owner lambda
        displacement a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor index := by
  let pair := rootCompletedDetectorTranslationPairData owner lambda
    displacement a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor
  rw [rootCompletedDetectorSoninTranslationTrace,
    ← rootCompletedDetectorTranslationPairData_traceProduct_eq owner lambda
      displacement a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor,
    ordinaryTraceAlong]
  apply tsum_congr
  intro index
  rw [pair.traceProduct_diagonal]
  rw [rootCompletedDetectorTranslationPhysicalDiagonal,
    ← sourceThreeBranchPairData_inner_eq_physicalPairing owner lambda a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
  dsimp only [pair]
  rw [rootCompletedDetectorTranslationPairData]
  simp only [BasisHilbertSchmidtPairData.smulRight,
    BasisHilbertSchmidtPairData.boundedSandwich,
    ContinuousLinearMap.comp_apply, neg_one_smul,
    ContinuousLinearMap.neg_apply, inner_neg_right]
  rw [(sourceBandProjection_isStarProjection lambda)
    |>.isSelfAdjoint.adjoint_eq]

end CCM24FiniteSRootCompletedDetectorPhysicalDiagonal
end CCM25Concrete
end Source
end ConnesWeilRH
