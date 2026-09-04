/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramParity

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramParity

open C1ClassGramOwner
open C1HboxRationalData

#print axioms classBump_neg
#print axioms legendrePoly_eval_neg_fin8
#print axioms classWindowFun_neg
#print axioms classGramEntry_zero_of_odd_parity
#print axioms zero_mem_odd_box_q28
#print axioms zero_mem_odd_box_q38
#print axioms zero_mem_odd_box_q48
#print axioms classGram_odd_bounds
#print axioms q28_classGram_odd_bounds

example (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    classGramEntry a ha i j = 0 :=
  classGramEntry_zero_of_odd_parity a ha i j hodd

example :
    GLo_q28 0 1 ≤ 0 ∧ 0 ≤ GHi_q28 0 1 := by
  exact zero_mem_odd_box_q28 0 1 (by norm_num)

end C1ClassGramParity
end Source
end ConnesWeilRH
