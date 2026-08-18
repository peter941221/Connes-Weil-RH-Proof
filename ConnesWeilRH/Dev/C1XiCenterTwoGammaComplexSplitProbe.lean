/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplit

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaComplexSplit

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

#print axioms realPartTest_apply
#print axioms imagPartTest_apply
#print axioms test_eq_realPart_add_I_imagPart
#print axioms laplaceAt_eq_realPart_add_I_imagPart
#print axioms laplaceAt_realPart_eq_zero_of_eq_zero
#print axioms laplaceAt_imagPart_eq_zero_of_eq_zero
#print axioms realPartTest_satisfies_laneRTripleVanishing
#print axioms imagPartTest_satisfies_laneRTripleVanishing
#print axioms convolutionSquare_re_split
#print axioms archimedeanNumerator_re_split
#print axioms archimedeanIntegrand_re_split
#print axioms archimedeanTerm_split
#print axioms gammaRArchProfileTerm_re_split
#print axioms gammaRArchProfileIntegral_re_split
#print axioms laneRFinitePrefixQuadraticValue_split

example (g : CompactLogTest) :
    (g.convolutionSquare.test 0).re =
      ((realPartTest g).convolutionSquare.test 0).re +
        ((imagPartTest g).convolutionSquare.test 0).re := by
  exact convolutionSquare_re_split g 0

end ConnesWeilRH.Source.C1XiCenterTwoGammaComplexSplit
