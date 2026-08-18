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
#print axioms laneRFinitePrefixQuadraticValue_nonpos_of_realValued_target

example (g : CompactLogTest) :
    realValuedTest (realPartTest g) := by
  exact realPartTest_realValued g

end ConnesWeilRH.Source.C1XiCenterTwoGammaComplexSplitReduction
