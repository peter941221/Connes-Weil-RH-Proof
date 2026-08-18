import ConnesWeilRH.Dev.C1XiCenterTwoGammaSummedKernel

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaSummedKernel

open MeasureTheory
open Set
open Filter
open C1SameOwnerWeil
open C1XiCenterTwoGamma
open CCM25Concrete.CompactLogConvolution

#print axioms integralOn_archimedeanIntegrand_eq_profilePrefix_add_tail
#print axioms tendsto_gammaRArchProfileTail_zero
#print axioms archimedeanTerm_eq_constant_add_profilePrefix_add_tail_re

example (F : CompactLogTest) (N : Nat) :
    (∫ y : Real in Ioi (0 : Real),
      C1SameOwnerWeil.archimedeanIntegrand F y) =
      (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n) +
        gammaRArchProfileTail F N :=
  integralOn_archimedeanIntegrand_eq_profilePrefix_add_tail F N

end ConnesWeilRH.Source.C1XiCenterTwoGammaSummedKernel
