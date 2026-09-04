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
#print axioms q38_GLo_le_three_halves_q28_GLo
#print axioms three_halves_q28_GHi_le_q38_GHi
#print axioms q48_GLo_le_two_q28_GLo
#print axioms two_q28_GHi_le_q48_GHi
#print axioms q38_GBounds_of_q28_GBounds
#print axioms q48_GBounds_of_q28_GBounds

example : classGramMatrix 2 (by norm_num) =
    (2 : ℝ) • classGramUnitMatrix :=
  classGramMatrix_scale 2 (by norm_num)

example (hG : ∀ i j, GLo_q28 i j ≤ classGramMatrix 2 (by norm_num) i j ∧
    classGramMatrix 2 (by norm_num) i j ≤ GHi_q28 i j) :
    ∀ i j, GLo_q38 i j ≤ classGramMatrix 3 (by norm_num) i j ∧
      classGramMatrix 3 (by norm_num) i j ≤ GHi_q38 i j :=
  q38_GBounds_of_q28_GBounds hG

end C1ClassGramScale
end Source
end ConnesWeilRH
