import ConnesWeilRH.Dev.C1XiCenterTwoGammaTailEstimate

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaTailEstimate

open C1XiCenterTwoGammaSummedKernel
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

#print axioms exists_gammaRArchProfileIntegral_norm_bound
#print axioms gammaRArchProfileTailNorm_le_explicit_majorant
#print axioms gammaRArchProfileTailNorm_le_explicit_rate

example (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ n : Nat, 0 < n →
        ‖gammaRArchProfileIntegral F n‖ ≤
          L * (((2 * (n : Real)) ^ 2)⁻¹) +
            2 * ‖F.test 0‖ *
              Real.exp (-((2 * (n : Real) + 1) * (supportRadius F + 1))) :=
  exists_gammaRArchProfileIntegral_norm_bound F

example (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ N : Nat, 0 < N →
        gammaRArchProfileTailNorm F N ≤
          gammaRArchProfileTailMajorant F L N :=
  gammaRArchProfileTailNorm_le_explicit_majorant F

example (F : CompactLogTest) :
    ∃ L : Real, 0 ≤ L ∧
      ∀ N : Nat, 0 < N →
        gammaRArchProfileTailNorm F N ≤
          gammaRArchProfileTailExplicitRate F L N :=
  gammaRArchProfileTailNorm_le_explicit_rate F

end ConnesWeilRH.Source.C1XiCenterTwoGammaTailEstimate
