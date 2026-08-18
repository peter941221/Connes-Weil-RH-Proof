import ConnesWeilRH.Dev.C1XiCenterTwoGammaMassRelativeTail

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaMassRelativeTail

open C1SameOwnerWeil
open C1XiCenterTwoGamma
open C1XiCenterTwoGammaSummedKernel
open CCM25Concrete.CompactLogConvolution

#print axioms convolutionSquare_zero_norm_eq_re
#print axioms gammaRArchProfileTailNorm_le_mass_scaled_rate
#print axioms gammaRArchProfileTerm_norm_le_mass_scaled_of_support_lipschitz
#print axioms gammaRArchProfileTailNorm_le_mass_scaled_rate_of_support_lipschitz
#print axioms archimedeanTerm_nonpos_of_mass_scaled_prefix_bound
#print axioms archimedeanTerm_neg_of_mass_scaled_prefix_bound

example (g : CompactLogTest) :
    ‖g.convolutionSquare.test 0‖ =
      (g.convolutionSquare.test 0).re :=
  convolutionSquare_zero_norm_eq_re g

example (g : CompactLogTest) (C : Real) (hC : 0 ≤ C)
    (hhead :
      ∀ (n : Nat) {y : Real},
        0 < y → y ≤ C1SameOwnerWeil.supportRadius g.convolutionSquare + 1 →
          ‖C1XiCenterTwoGamma.gammaRArchProfileTerm
              g.convolutionSquare n y‖ ≤
            C * (g.convolutionSquare.test 0).re * y *
              Real.exp (-(2 * (n : Real) * y)))
    (N : Nat) (hN : 0 < N) :
    C1XiCenterTwoGammaSummedKernel.gammaRArchProfileTailNorm
        g.convolutionSquare N ≤
      gammaRArchProfileTailMassRate g C N :=
  gammaRArchProfileTailNorm_le_mass_scaled_rate g C hC hhead N hN

end ConnesWeilRH.Source.C1XiCenterTwoGammaMassRelativeTail
