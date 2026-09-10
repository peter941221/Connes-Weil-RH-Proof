import ConnesWeilRH.Dev.C1G8P1MetricProjectionDefectLedger

/-!
# G8 P1 projected--complement trace-class owner

The projection-defect ledger has an ordered mixed term whose left leg is the
projected cutoff and whose right leg is the detector applied to the
complement. This leaf supplies that term with an explicit Hilbert--Schmidt
pair owner, so its ordinary trace is legal without any cyclicity shortcut.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1MetricProjectionDefectTraceClass

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open C1G8AdjointShearGram
open C1G8P1MetricProjectionFactorization
open C1G8P1MetricProjectionDefectLedger
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable def g8SourceCutoffProjectedComplementCrossPairData
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis := by
  let A :=
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let J := sourceInclusion lambda
  let C := J† ∘L A
  let K := J ∘L C
  let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
  let G := g8AdjointShearGram owner lambda family
  have hA :=
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left_summable_normSq
  have hC : Summable fun i => ‖C (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis A
      (ContinuousLinearMap.adjoint J) hA
  have hK : Summable fun i => ‖K (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis C J hC
  have hD : Summable fun i => ‖D (sourceBasis i)‖ ^ 2 := by
    exact g8SourceCutoffComplementLeg_summable_normSq owner lambda family
      globalBasis sourceBasis n
  have hGD : Summable fun i => ‖(G ∘L D) (sourceBasis i)‖ ^ 2 := by
    exact PositiveTrace.summable_normSq_postcomp sourceBasis D G hD
  exact
    { left := K
      right := G ∘L D
      left_summable_normSq := hK
      right_summable_normSq := hGD }

theorem g8SourceCutoffProjectedComplementCrossPairData_traceProduct_eq
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8SourceCutoffProjectedComplementCrossPairData owner lambda family
      globalBasis sourceBasis n).traceProduct =
      (g8MetricCutoffProjectedLeg owner lambda family globalBasis sourceBasis n)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n := by
  simp only [g8SourceCutoffProjectedComplementCrossPairData,
    BasisHilbertSchmidtPairData.traceProduct, g8MetricCutoffProjectedLeg]

theorem g8SourceCutoffProjectedComplementCrossPairData_isTraceClassAlong
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    IsTraceClassAlong sourceBasis
      (g8SourceCutoffProjectedComplementCrossPairData owner lambda family
        globalBasis sourceBasis n).traceProduct := by
  exact (g8SourceCutoffProjectedComplementCrossPairData owner lambda family
    globalBasis sourceBasis n).traceProduct_isTraceClassAlong

theorem g8ProjectionDefectChannels_isTraceClassAlong
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
     IsTraceClassAlong sourceBasis (C† ∘L J† ∘L G ∘L D)) ∧
    (let C := (sourceInclusion lambda)† ∘L
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
     let J := sourceInclusion lambda
     let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
     let G := g8AdjointShearGram owner lambda family
     IsTraceClassAlong sourceBasis (D† ∘L G ∘L J ∘L C)) ∧
    (let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
     let G := g8AdjointShearGram owner lambda family
     IsTraceClassAlong sourceBasis (D† ∘L G ∘L D)) := by
  dsimp only
  constructor
  · simpa only [g8SourceCutoffProjectedComplementCrossPairData,
      BasisHilbertSchmidtPairData.traceProduct, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.comp_assoc] using
      g8SourceCutoffProjectedComplementCrossPairData_isTraceClassAlong
        owner lambda family globalBasis sourceBasis n
  constructor
  · simpa only [ContinuousLinearMap.comp_assoc] using
      g8SourceCutoffComplementCrossPairData_isTraceClassAlong
        owner lambda family globalBasis sourceBasis n
  · simpa only [ContinuousLinearMap.comp_assoc] using
      g8SourceCutoffComplementLeakagePairData_isTraceClassAlong
        owner lambda family globalBasis sourceBasis n

end
end C1G8P1MetricProjectionDefectTraceClass
end Source
end ConnesWeilRH
