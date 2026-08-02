/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalLeakageTraceReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramOrderingBridge

/-!
# Actual target-commutator reduction for the finite-S Gate trace

The complete physical leakage is the adjoint of the existing actual
target-commutator owner.  This removes the restricted inverse Gram from the
active ordinary-trace target without cycling an infinite-dimensional trace.

The resulting owner keeps the inverse transport, target projection
commutator, and forward transport in one product.  No factorwise norm estimate
or family-uniform bound is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalTargetCommutatorReduction

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
open CCM24FiniteSGatePhysicalSignedDiagonal
open CCM24FiniteSGatePhysicalLeakageTraceReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSRawCompletedGaugeOwner
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private theorem adjoint_neg_eq_neg_adjoint_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (operator : H →L[ℂ] H) :
    (-operator)† = -(operator†) := by
  apply ContinuousLinearMap.ext
  intro u
  exact ext_inner_right ℂ fun v => by
    simp only [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right]

/-- The complete physical leakage is, in the exact Hilbert-space orientation,
the adjoint of the actual target-commutator response. -/
theorem sourceGatePhysicalLeakageCrossingResponse_adjoint_eq_targetCommutator
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (sourceGatePhysicalLeakageCrossingResponse owner lambda family)† =
      finiteEulerTargetCommutatorResponse owner lambda family := by
  rw [sourceGatePhysicalLeakageCrossingResponse_eq_neg_sourceBandGramResponse,
    adjoint_neg_eq_neg_adjoint_local,
    ← leftOrderedSourceBandGramResponse_eq_adjoint,
    leftOrderedSourceBandGramResponse_eq_neg_targetCommutator]
  simp only [neg_neg]

/-- Adjoint passage conjugates the ordinary diagonal trace.  This is a direct
series identity and does not use a trace cycle. -/
theorem ordinaryTraceAlong_targetCommutator_eq_star_leakage
    {ρ : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family) =
      star (ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse owner lambda family)) := by
  rw [← sourceGatePhysicalLeakageCrossingResponse_adjoint_eq_targetCommutator,
    ordinaryTraceAlong_adjoint]

/-- The active absolute leakage trace is exactly the absolute trace of the
actual target-commutator product. -/
theorem norm_ordinaryTraceAlong_targetCommutator_eq_leakage
    {ρ : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse owner lambda family)‖ =
      ‖ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse owner lambda family)‖ := by
  rw [ordinaryTraceAlong_targetCommutator_eq_star_leakage,
    Complex.star_def, Complex.norm_conj]

/-- Fixed-family trace legality transfers from the complete leakage to the
actual target-commutator owner. -/
theorem targetCommutatorResponse_isTraceClassAlong_of_leakage
    {ρ : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hleakage : IsTraceClassAlong sourceBasis
      (sourceGatePhysicalLeakageCrossingResponse owner lambda family)) :
    IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda family) := by
  rw [← sourceGatePhysicalLeakageCrossingResponse_adjoint_eq_targetCommutator]
  exact isTraceClassAlong_adjoint sourceBasis _ hleakage

/-- Family-uniform boundedness of the complete leakage trace is equivalent to
family-uniform boundedness of the actual target-commutator trace. -/
theorem exists_uniform_leakageTraceBound_iff_targetCommutatorTraceBound
    {ρ : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (sourceGatePhysicalLeakageCrossingResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse
          owner lambda family)‖ ≤ bound) := by
  constructor
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, ?_⟩
    intro family
    rw [norm_ordinaryTraceAlong_targetCommutator_eq_leakage]
    exact hbound family
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, ?_⟩
    intro family
    rw [← norm_ordinaryTraceAlong_targetCommutator_eq_leakage]
    exact hbound family

/-- Proof 742's Gate reduction can therefore be stated directly with the
actual target projection commutator.  The whole target product remains signed
and no transport factor is estimated separately. -/
theorem exists_uniform_lowerFactorGaugedTraceBound_iff_targetCommutatorTraceBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤ bound) ↔
    (∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
      ‖ordinaryTraceAlong sourceBasis
        (finiteEulerTargetCommutatorResponse
          owner lambda family)‖ ≤ bound) := by
  calc
    _ ↔ ∃ bound : ℝ, ∀ family : FinitePrimePowerFamily,
        ‖ordinaryTraceAlong sourceBasis
          (sourceGatePhysicalLeakageCrossingResponse
            owner lambda family)‖ ≤ bound :=
      exists_uniform_lowerFactorGaugedTraceBound_iff_leakageTraceBound
        owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    _ ↔ _ :=
      exists_uniform_leakageTraceBound_iff_targetCommutatorTraceBound
        owner lambda sourceBasis

end CCM24FiniteSGatePhysicalTargetCommutatorReduction
end CCM25Concrete
end Source
end ConnesWeilRH
