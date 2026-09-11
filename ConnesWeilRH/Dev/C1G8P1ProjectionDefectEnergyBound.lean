import ConnesWeilRH.Dev.C1G8P1ProjectionDefectCommutator
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

/-!
# G8 P1 projection-defect energy bound

The sole signed defect channel is a Hilbert--Schmidt Cauchy--Schwarz product.
After commutator localization, its real trace is bounded by the geometric mean
of two explicit same-owner energies.  The missing analytic input is a useful
cutoff bound (or vanishing) for those energies, not trace legality.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1ProjectionDefectEnergyBound

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open C1G8AdjointShearGram
open C1G8P1MetricProjectionFactorization
open C1G8P1MetricProjectionDefectTraceClass
open C1G8P1ProjectionDefectCommutator
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The two named Hilbert--Schmidt energies governing the signed projection
defect cross channel. -/
noncomputable def g8ProjectionDefectCrossLeftEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) : ℝ :=
  ∑' i, ‖(g8SourceCutoffProjectedComplementCrossPairData owner lambda family
    globalBasis sourceBasis n).left (sourceBasis i)‖ ^ 2

noncomputable def g8ProjectionDefectCrossRightEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) : ℝ :=
  ∑' i, ‖(g8SourceCutoffProjectedComplementCrossPairData owner lambda family
    globalBasis sourceBasis n).right (sourceBasis i)‖ ^ 2

/-- The signed projection-defect trace is controlled by the geometric mean of
its two explicit same-owner Hilbert--Schmidt energies. -/
theorem abs_re_ordinaryTraceAlong_g8ProjectionDefectCross_le_geometricEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    |(ordinaryTraceAlong sourceBasis
      ((g8MetricCutoffProjectedLeg owner lambda family globalBasis sourceBasis n)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n)).re| ≤
      Real.sqrt (g8ProjectionDefectCrossLeftEnergy owner lambda family globalBasis
        sourceBasis n) *
        Real.sqrt (g8ProjectionDefectCrossRightEnergy owner lambda family globalBasis
          sourceBasis n) := by
  let pair := g8SourceCutoffProjectedComplementCrossPairData owner lambda family
    globalBasis sourceBasis n
  have htrace := ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy pair
  rw [g8SourceCutoffProjectedComplementCrossPairData_traceProduct_eq] at htrace
  exact (Complex.abs_re_le_norm _).trans (by
    simpa only [pair, g8ProjectionDefectCrossLeftEnergy,
      g8ProjectionDefectCrossRightEnergy] using htrace)

/- The commutator spelling expands the same source-cutoff owner. -/
set_option maxHeartbeats 1000000 in
-- The preceding Cauchy--Schwarz bound applies to the commutator-localized
-- form of the sole signed defect channel.
theorem abs_re_ordinaryTraceAlong_g8ProjectionDefectCommutator_le_geometricEnergy
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    |(ordinaryTraceAlong sourceBasis
      (let A := (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
       let J := sourceInclusion lambda
       let C := J† ∘L A
       let D := g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n
       let G := g8AdjointShearGram owner lambda family
       let P := sourceSoninProjection lambda
       C† ∘L J† ∘L (P ∘L G - G ∘L P) ∘L D)).re| ≤
      Real.sqrt (g8ProjectionDefectCrossLeftEnergy owner lambda family globalBasis
        sourceBasis n) *
        Real.sqrt (g8ProjectionDefectCrossRightEnergy owner lambda family globalBasis
          sourceBasis n) := by
  rw [← g8ProjectionDefectCross_eq_sourceProjection_commutator]
  simpa only [g8MetricCutoffProjectedLeg, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc] using
    abs_re_ordinaryTraceAlong_g8ProjectionDefectCross_le_geometricEnergy owner
      lambda family globalBasis sourceBasis n

end
end C1G8P1ProjectionDefectEnergyBound
end Source
end ConnesWeilRH
