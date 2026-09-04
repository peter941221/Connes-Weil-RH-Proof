/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Q28ClassGramIntervalTransfer

namespace ConnesWeilRH
namespace Source
namespace C1Q28ClassGramIntervalTransferAudit

open C1Q28ClassGramIntervalTransfer
open C1ClassGramMomentReduction
open C1HboxRationalData
open Matrix

#print axioms q28Moment0Lo
#print axioms q28Moment0Hi
#print axioms q28Moment2Lo
#print axioms q28Moment2Hi
#print axioms q28_classGramModel_bounds_of_baseMomentBounds
#print axioms q28_classGram_bounds_of_baseMomentBounds
#print axioms q28_hbox_of_baseMomentBounds

example :
    q28Moment0Lo ≤ classMoment 0 ∧ classMoment 0 ≤ q28Moment0Hi →
      q28Moment2Lo ≤ classMoment 2 ∧ classMoment 2 ≤ q28Moment2Hi →
      ∀ i j : Fin 8,
        GLo_q28 i j ≤ classGramMatrix 2 (by norm_num) i j ∧
          classGramMatrix 2 (by norm_num) i j ≤ GHi_q28 i j := by
  intro hI0 hI2
  exact q28_classGram_bounds_of_baseMomentBounds hI0 hI2

end C1Q28ClassGramIntervalTransferAudit
end Source
end ConnesWeilRH
