/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorCommutator

/-!
# Trace owner for one completed detector displacement

The fixed physical three-branch pair owns the detector/Sonin commutator.
Bounded sandwiching by the quotient band and one causal translation therefore
gives a genuine Hilbert--Schmidt pair for every displacement atom in Proof 467.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorTrace

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedDetectorCommutator

/-- The physical three-branch pair, sandwiched by the two quotient-band legs
and the causal translation, owns one completed detector displacement atom. -/
noncomputable def rootCompletedDetectorTranslationPairData
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
    BasisHilbertSchmidtPairData
      (G := commonBoundaryCarrier a c) globalBasis :=
  ((sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor).boundedSandwich
    boundaryBasis (sourceBandProjection lambda)
      ((cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap ∘L
        sourceBandProjection lambda)).smulRight (-1)

/-- The transported physical pair has exactly the Proof 467 displacement atom
as its trace product. -/
theorem rootCompletedDetectorTranslationPairData_traceProduct_eq
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
    (rootCompletedDetectorTranslationPairData owner lambda displacement a c
      hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor).traceProduct =
        rootCompletedDetectorSoninTranslationPair owner lambda displacement := by
  have hcommutator :
      CCM24FiniteSTwoSidedRootRecombination.commutator
          (detectorOperator owner) (sourceSoninProjection lambda) =
        -cc20Commutator (sourceSoninProjection lambda)
          (detectorOperator owner) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [CCM24FiniteSTwoSidedRootRecombination.commutator,
      cc20Commutator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply]
    abel
  rw [rootCompletedDetectorTranslationPairData,
    BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
    BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
    sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor,
    ← sourceSoninCommutator_eq_threeBranch]
  rw [rootCompletedDetectorSoninTranslationPair, hcommutator]
  apply ContinuousLinearMap.ext
  intro u
  simp only [neg_one_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_neg]

/-- Every completed detector displacement atom is trace class along the named
global basis, with no additional Hilbert--Schmidt premise. -/
theorem rootCompletedDetectorSoninTranslationPair_isTraceClassAlong
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
    IsTraceClassAlong globalBasis
      (rootCompletedDetectorSoninTranslationPair owner lambda displacement) := by
  rw [← rootCompletedDetectorTranslationPairData_traceProduct_eq owner lambda
    displacement a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor]
  exact (rootCompletedDetectorTranslationPairData owner lambda displacement a c
    hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    hfactor).traceProduct_isTraceClassAlong

/-- The ordinary trace of one displacement atom, now backed by the explicit
physical Hilbert--Schmidt pair. -/
noncomputable def rootCompletedDetectorSoninTranslationTrace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : ℂ :=
  ordinaryTraceAlong globalBasis
    (rootCompletedDetectorSoninTranslationPair owner lambda displacement)

end CCM24FiniteSRootCompletedDetectorTrace
end CCM25Concrete
end Source
end ConnesWeilRH
