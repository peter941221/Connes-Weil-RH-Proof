import ConnesWeilRH.Dev.C1XiCenterTwoGammaDerivativeEnergy

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaDerivativeEnergy

open C1SameOwnerWeil
open C1XiCenterTwoGammaSummedKernel
open C1XiCenterTwoGammaTailEstimate
open CCM25Concrete.CompactLogConvolution

#print axioms compactLogDerivativeEnergy
#print axioms convolutionSquareDerivativeEnergyCoefficient
#print axioms norm_deriv_convolutionSquare_le_derivativeEnergyCoefficient
#print axioms convolutionSquare_support_lipschitz_of_derivative_energy
#print axioms convolutionSquareDerivativeEnergyProfileConstant
#print axioms gammaRArchProfileTailNorm_le_derivativeEnergy_rate

example (g : CompactLogTest) (x : Real) :
    ‖deriv (g.convolutionSquare.test) x‖ ≤
      convolutionSquareDerivativeEnergyCoefficient g :=
  norm_deriv_convolutionSquare_le_derivativeEnergyCoefficient g x

example (g : CompactLogTest) (N : Nat) (hN : 0 < N) :
    gammaRArchProfileTailNorm g.convolutionSquare N ≤
      gammaRArchProfileTailExplicitRate g.convolutionSquare
        (convolutionSquareDerivativeEnergyProfileConstant g) N :=
  gammaRArchProfileTailNorm_le_derivativeEnergy_rate g N hN

end ConnesWeilRH.Source.C1XiCenterTwoGammaDerivativeEnergy
