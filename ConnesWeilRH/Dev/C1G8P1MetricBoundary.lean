import ConnesWeilRH.Dev.C1G8P1TraceLedger

/-!
# G8 P1 literal-cutoff metric boundary form

The P1 finite-prime comparison must start with the actual cutoff metric
sandwich, not with an uncut projection response.  This leaf rewrites that
literal operator through the existing finite Euler survivor and boundary sum.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1MetricBoundary

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSCoframeResponse
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSGramInverseCalculus
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open CCM25Concrete.CCM24FiniteSTransportBounds
open C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The literal P1 metric term of the physical endpoint, before any trace is
taken. -/
noncomputable def g8PhysicalMetricCutoffOperator
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  let C := (sourceInclusion lambda)† ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  C† ∘L ((finiteEulerMetricCoframe lambda family)† ∘L
    detectorOperator owner ∘L finiteEulerMetricCoframe lambda family) ∘L C

theorem g8PhysicalMetricCutoffOperator_isPositive
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n).IsPositive := by
  let C := (sourceInclusion lambda)† ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let E := finiteEulerMetricCoframe lambda family
  unfold g8PhysicalMetricCutoffOperator
  change ((C† ∘L E†) ∘L detectorOperator owner ∘L E ∘L C).IsPositive
  have h := (detectorOperator_isPositive_for_g8 owner).adjoint_conj (E ∘L C)
  simpa only [C, E, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc] using h

/-- The literal cutoff metric term is exactly the finite-Euler survivor plus
finite boundary-sum Gram.  No trace or finite-prime scalar is asserted. -/
theorem g8PhysicalMetricCutoffOperator_eq_survivorBoundaryGram
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n =
      let C := (sourceInclusion lambda)† ∘L
        (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
      let E := (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (newSuffixFrame lambda [] ∘L
          (suffixEulerTransitionProduct lambda family.visiblePrimes)† ∘L
            parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes (by norm_num) +
          (finiteEulerMetricCoframeBoundaryMaps lambda family).sum)
      C† ∘L E† ∘L detectorOperator owner ∘L E ∘L C := by
  rw [g8PhysicalMetricCutoffOperator]
  rw [finiteEulerMetricCoframe_eq_survivor_add_boundarySum]
  rfl

end
end C1G8P1MetricBoundary
end Source
end ConnesWeilRH
