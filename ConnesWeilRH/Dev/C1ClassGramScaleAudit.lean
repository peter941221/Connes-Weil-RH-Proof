/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramScale

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramScale

#print axioms classGramUnitEntry
#print axioms classGramUnitMatrix
#print axioms classGramUnitEntry_apply
#print axioms classWindowFun_scale
#print axioms classGramEntry_scale
#print axioms classGramMatrix_scale
#print axioms classGramBounds_of_unitBounds
#print axioms three_halves_q28_GLo_le_q38_GLo
#print axioms q38_GHi_le_three_halves_q28_GHi
#print axioms two_q28_GLo_le_q48_GLo
#print axioms q48_GHi_le_two_q28_GHi

example : classGramMatrix 2 (by norm_num) =
    (2 : ℝ) • classGramUnitMatrix :=
  classGramMatrix_scale 2 (by norm_num)

end C1ClassGramScale
end Source
end ConnesWeilRH
