/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplitReduction

namespace ConnesWeilRH.Source.C1XiCenterTwoGammaComplexSplitReduction

open ConnesWeilRH.Source.C1XiCenterTwoGammaComplexSplit
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

#print axioms realPartTest_realValued
#print axioms imagPartTest_realValued
#print axioms realPartTest_support_subset
#print axioms imagPartTest_support_subset
#print axioms primeFreeSquare_of_support_Icc
#print axioms componentPrimeFreeSquare_of_support_Icc
#print axioms componentPrimeFreeSquare_tripleVanishingRoot_of_Icc
#print axioms laneRFinitePrefixQuadraticValue_nonpos_of_realValued_target
#print axioms laneRFinitePrefixQuadraticValue_nonpos_tripleVanishingRoot_of_realValued_target

example (g : CompactLogTest) :
    realValuedTest (realPartTest g) := by
  exact realPartTest_realValued g

end ConnesWeilRH.Source.C1XiCenterTwoGammaComplexSplitReduction
