import ConnesWeilRH.Dev.C1G8AdjointShearGram
import ConnesWeilRH.Dev.C1P2BilateralProfile

/-!
# G8 to P2 aggregate exit

This leaf is the exact same-owner consumer from the G8 positive-trace
readback to the signed bilateral-profile inequality.  It supplies no
readback data and hence no producer or RH conclusion by itself.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P2AggregateExit

open C1G8AdjointShearGram
open C1P2BilateralProfile
open C1HealthyYoshidaDetector
open C1SameOwnerWeil
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

theorem p2Aggregate_nonpos_of_g8SameOwnerReadbackData
    {ν ρ : Type*}
    (rho : ℂ)
    (owner : CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ
      ℂ (sourceSoninCarrier lambda))
    (data : G8SameOwnerReadbackData owner lambda family globalBasis sourceBasis)
    (hdetector : HealthyYoshidaDetectorData rho owner.sourceTest) :
    archimedeanTerm owner.sourceTest.convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet owner.sourceTest.convolutionSquare,
          ArithmeticFunction.vonMangoldt n *
              (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile owner.sourceTest.convolutionSquare
              (Real.log n)).re ≤ 0 := by
  have hqw : 0 ≤ C1SameOwnerWeil.qw owner.sourceTest :=
    qw_nonnegative_of_g8SameOwnerReadbackData owner lambda family
      globalBasis sourceBasis data
  exact (qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
    owner.sourceTest hdetector.vanishesOnF).mp hqw

end
end C1G8P2AggregateExit
end Source
end ConnesWeilRH
