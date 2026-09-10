import ConnesWeilRH.Dev.C1G8P1MetricBoundary

/-!
# G8 P1 projected-cutoff factorization

The literal metric cutoff uses the cutoff leg after compression to the
source-Sonin carrier.  This leaf rewrites it as an adjoint conjugation of the
ambient `g8AdjointShearGram` by that projected leg.  It is an exact
same-owner factorization; it does not identify the projected leg with the
uncompressed cutoff leg and therefore does not claim finite-trace equality.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1MetricProjectionFactorization

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSCoframeResponse
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSTransportBounds
open C1G8AdjointShearGram
open C1G8P1MetricBoundary
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The finite-window cutoff leg after compression to the source-Sonin
carrier.  Its ambient image is the source-subspace projection of the raw
cutoff leg, which is the exact place where a future trace comparison must
control a projection defect. -/
noncomputable def g8MetricCutoffProjectedLeg
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  sourceInclusion lambda ∘L
    ((sourceInclusion lambda)† ∘L
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left)

theorem g8PhysicalMetricCutoffOperator_eq_projectedLeg_adjoint_gram_projectedLeg
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n =
      (g8MetricCutoffProjectedLeg owner lambda family globalBasis sourceBasis n)† ∘L
        g8AdjointShearGram owner lambda family ∘L
          g8MetricCutoffProjectedLeg owner lambda family globalBasis sourceBasis n := by
  let C := (sourceInclusion lambda)† ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let J := sourceInclusion lambda
  have hcompress : J† ∘L g8AdjointShearGram owner lambda family ∘L J =
      (finiteEulerMetricCoframe lambda family)† ∘L
        detectorOperator owner ∘L finiteEulerMetricCoframe lambda family := by
    exact sourceCompression_g8AdjointShearGram_eq_metricCoframeGram
      owner lambda family
  unfold g8PhysicalMetricCutoffOperator g8MetricCutoffProjectedLeg
  change C† ∘L
      ((finiteEulerMetricCoframe lambda family)† ∘L
        detectorOperator owner ∘L finiteEulerMetricCoframe lambda family) ∘L C =
    (J ∘L C)† ∘L g8AdjointShearGram owner lambda family ∘L (J ∘L C)
  calc
    C† ∘L
        ((finiteEulerMetricCoframe lambda family)† ∘L
          detectorOperator owner ∘L finiteEulerMetricCoframe lambda family) ∘L C =
      C† ∘L (J† ∘L g8AdjointShearGram owner lambda family ∘L J) ∘L C := by
        simpa only [ContinuousLinearMap.comp_assoc] using
          congrArg (fun T => C† ∘L T ∘L C) hcompress.symm
    _ = (J ∘L C)† ∘L g8AdjointShearGram owner lambda family ∘L (J ∘L C) := by
      simp only [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- The raw same-owner cutoff leg splits exactly into its source-projected
part and the complementary source-projection defect. -/
theorem g8SourceCutoffPairData_left_eq_projected_add_complement
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left =
      g8MetricCutoffProjectedLeg owner lambda family globalBasis sourceBasis n +
        g8SourceCutoffComplementLeg owner lambda family globalBasis sourceBasis n := by
  unfold g8MetricCutoffProjectedLeg g8SourceCutoffComplementLeg
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply]
  abel

end
end C1G8P1MetricProjectionFactorization
end Source
end ConnesWeilRH
