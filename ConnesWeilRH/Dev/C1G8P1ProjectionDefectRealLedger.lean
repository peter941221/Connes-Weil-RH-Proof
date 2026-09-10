import ConnesWeilRH.Dev.C1G8P1MetricProjectionDefectTraceLedger

/-!
# G8 P1 projection-defect real ledger

The three projection-defect trace channels consist of an adjoint pair and a
positive diagonal channel.  This leaf records that reduction on the named
source basis.  It does not bound the remaining real cross trace: that bound is
the analytic P1 obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1ProjectionDefectRealLedger

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open C1G8AdjointShearGram
open C1G8P1MetricBoundary
open C1G8P1MetricChannels
open C1G8P1MetricProjectionDefectLedger
open C1G8P1MetricProjectionDefectTraceClass
open C1G8P1MetricProjectionDefectTraceLedger
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/- The expanded same-owner adjoint expressions need more elaboration budget. -/
set_option maxHeartbeats 1000000 in
-- The two ordered projected--complement defect channels are adjoints on the
-- same healthy source owner.
theorem g8ProjectionDefectSecond_eq_first_adjoint
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (let C := (sourceInclusion lambda)† ∘L
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
     let J := sourceInclusion lambda
     let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
     let G := g8AdjointShearGram owner lambda family
     D† ∘L G ∘L J ∘L C) =
    (let C := (sourceInclusion lambda)† ∘L
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
     let J := sourceInclusion lambda
     let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
     let G := g8AdjointShearGram owner lambda family
     (C† ∘L J† ∘L G ∘L D)†) := by
  dsimp only
  simp only [ContinuousLinearMap.adjoint_comp,
    (g8AdjointShearGram_isPositive owner lambda family).isSelfAdjoint.adjoint_eq,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/- The trace expression expands several owner-local let bindings. -/
set_option maxHeartbeats 1000000 in
-- After ordinary trace, the two ordered projection cross channels collapse
-- to twice the real part of the first one.
theorem ordinaryTraceAlong_g8ProjectionDefectCrossPair_eq_two_re
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (let C := (sourceInclusion lambda)† ∘L
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
         let J := sourceInclusion lambda
         let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
         let G := g8AdjointShearGram owner lambda family
         C† ∘L J† ∘L G ∘L D + D† ∘L G ∘L J ∘L C) =
      ((2 * (ordinaryTraceAlong sourceBasis
        (let C := (sourceInclusion lambda)† ∘L
          (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
         let J := sourceInclusion lambda
         let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
         let G := g8AdjointShearGram owner lambda family
         C† ∘L J† ∘L G ∘L D)).re : ℝ) : ℂ) := by
  have hdef := g8ProjectionDefectChannels_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  rcases hdef with ⟨hfirst, hsecond, _⟩
  dsimp only at hfirst hsecond ⊢
  rw [ordinaryTraceAlong_add sourceBasis _ _ hfirst hsecond]
  rw [g8ProjectionDefectSecond_eq_first_adjoint]
  rw [ordinaryTraceAlong_adjoint, Complex.star_def, Complex.add_conj]

/-- The diagonal projection-defect channel is positive, hence has nonnegative
ordinary trace real part. -/
theorem g8ProjectionDefectDiagonal_trace_re_nonnegative
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
       let G := g8AdjointShearGram owner lambda family
       D† ∘L G ∘L D)).re := by
  let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
  let G := g8AdjointShearGram owner lambda family
  have hpositive : (D† ∘L G ∘L D).IsPositive := by
    simpa only [D, G] using
      (g8AdjointShearGram_isPositive owner lambda family).adjoint_conj D
  have htrace : IsTraceClassAlong sourceBasis (D† ∘L G ∘L D) := by
    have hdef := g8ProjectionDefectChannels_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n
    simpa only [D, G, ContinuousLinearMap.comp_assoc] using
      hdef.2.2
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum htrace]
  exact tsum_nonneg (fun i => hpositive.re_inner_nonneg_right (sourceBasis i))

end

end C1G8P1ProjectionDefectRealLedger
end Source
end ConnesWeilRH
