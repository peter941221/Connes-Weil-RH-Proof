import ConnesWeilRH.Dev.C1XiCenterTwoGammaPrefixTailConsumer

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaPrefixTailConsumer

open C1XiCenterTwoGammaSummedKernel
open CCM25Concrete.CompactLogConvolution

#print axioms archimedeanTerm_nonpos_of_profilePrefix_bound_and_tailNorm_bound
#print axioms archimedeanTerm_neg_of_profilePrefix_bound_and_tailNorm_bound

example (F : CompactLogTest) (N : Nat) (budget : Real)
    (hprefix :
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0).re) +
        (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n).re ≤ -budget)
    (htail : gammaRArchProfileTailNorm F N ≤ budget) :
    C1SameOwnerWeil.archimedeanTerm F ≤ 0 :=
  archimedeanTerm_nonpos_of_profilePrefix_bound_and_tailNorm_bound
    F N budget hprefix htail

example (F : CompactLogTest) (N : Nat) (budget delta : Real)
    (hdelta : 0 < delta)
    (hprefix :
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0).re) +
        (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n).re ≤
          -(budget + delta))
    (htail : gammaRArchProfileTailNorm F N ≤ budget) :
    C1SameOwnerWeil.archimedeanTerm F < 0 :=
  archimedeanTerm_neg_of_profilePrefix_bound_and_tailNorm_bound
    F N budget delta hdelta hprefix htail

end ConnesWeilRH.Source.C1XiCenterTwoGammaPrefixTailConsumer
