import ConnesWeilRH.Dev.C1G8P2AggregateExit

/-!
# G8 P3 same-detector contradiction

The G8 readback consumer and the healthy detector negativity are now composed
on the identical selected owner.  This is the logical P3 capstone; it does
not construct the missing readback data.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P3Contradiction

open C1G8AdjointShearGram
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1CenterTwoCriterionBridge
open CC20Concrete
open CCM25Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.SelectedWeilSquare
open scoped BigOperators

noncomputable section

theorem false_of_g8SameOwnerReadbackData_and_healthyDetector
    {ν ρ : Type*}
    (rho : ℂ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (readback : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis)
    (hdetector : HealthyYoshidaDetectorData rho owner.sourceTest) : False := by
  have hnonnegative : 0 ≤ C1SameOwnerWeil.qw owner.sourceTest :=
    qw_nonnegative_of_g8SameOwnerReadbackData owner lambda family
      globalBasis sourceBasis readback
  have hspectralNegative :
      C1SpectralWeil.spectralWeilValue owner.sourceTest.convolutionSquare < 0 :=
    (weilSquareSumPositive_iff_spectralWeilValue_neg owner.sourceTest).mp
      hdetector.weilSquareSumPositive
  have hnegative : C1SameOwnerWeil.qw owner.sourceTest < 0 := by
    rw [qw_eq_spectralWeilValue_centerTwo]
    exact hspectralNegative
  exact (not_lt_of_ge hnonnegative) hnegative

end
end C1G8P3Contradiction
end Source
end ConnesWeilRH
