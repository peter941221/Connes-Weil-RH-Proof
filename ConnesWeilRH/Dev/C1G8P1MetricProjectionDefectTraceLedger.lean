import ConnesWeilRH.Dev.C1G8P1MetricProjectionDefectTraceClass

/-!
# G8 P1 metric projection-defect trace ledger

With the three defect channels placed under explicit Hilbert--Schmidt owners,
the operator ledger can be read on the named source basis. This is an exact
ordinary-trace identity; it still leaves the defect signs and cutoff limit as
the analytic P1 obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1MetricProjectionDefectTraceLedger

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
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
theorem ordinaryTraceAlong_g8SourceCutoffPairData_traceProduct_eq_metric_add_projectionDefect
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).traceProduct =
      ordinaryTraceAlong sourceBasis
          (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n) +
        ordinaryTraceAlong sourceBasis
          (let C := (sourceInclusion lambda)† ∘L
            (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
           let J := sourceInclusion lambda
           let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
           let G := g8AdjointShearGram owner lambda family
           C† ∘L J† ∘L G ∘L D) +
        ordinaryTraceAlong sourceBasis
          (let C := (sourceInclusion lambda)† ∘L
            (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
           let J := sourceInclusion lambda
           let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
           let G := g8AdjointShearGram owner lambda family
           D† ∘L G ∘L J ∘L C) +
        ordinaryTraceAlong sourceBasis
          (let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
           let G := g8AdjointShearGram owner lambda family
           D† ∘L G ∘L D) := by
  have hledger := g8SourceCutoffPairData_traceProduct_eq_metric_add_projectionDefect
    owner lambda family globalBasis sourceBasis n
  have hmetric := g8PhysicalMetricCutoffOperator_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  have hdef := g8ProjectionDefectChannels_isTraceClassAlong
    owner lambda family globalBasis sourceBasis n
  rcases hdef with ⟨h1, h2, h3⟩
  dsimp only at h1 h2 h3 ⊢
  simp only [add_assoc] at hledger ⊢
  have h23 := isTraceClassAlong_add sourceBasis _ _ h2 h3
  have h123 := isTraceClassAlong_add sourceBasis _ _ h1 h23
  rw [hledger]
  rw [ordinaryTraceAlong_add sourceBasis _ _ hmetric h123]
  rw [ordinaryTraceAlong_add sourceBasis _ _ h1 h23]
  rw [ordinaryTraceAlong_add sourceBasis _ _ h2 h3]

end
end C1G8P1MetricProjectionDefectTraceLedger
end Source
end ConnesWeilRH
