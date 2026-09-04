/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramMomentReduction

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramMomentReductionAudit

open C1ClassGramMomentReduction

#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.classBump_hasCompactSupport
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.classUnitWeight_contDiff
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.classMoment_integrable
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.classMoment_odd_zero
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.hasDerivAt_classBump
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.hasDerivAt_classUnitWeight
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.momentIBPCore_hasDerivAt
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.classMoment_recurrence
#print axioms ConnesWeilRH.Source.C1ClassGramMomentReduction.classMoment_even_step

example :
    classMoment_even_step 0 =
      2 * classMoment 2 - ((1 : ℝ) / 5) * classMoment 0 := by
  norm_num [classMoment_even_step]

example (n : ℕ) :
    classMoment (2 * n + 4) =
      2 * classMoment (2 * n + 2) -
        ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 5)) * classMoment (2 * n) :=
  classMoment_even_step n

end C1ClassGramMomentReductionAudit
end Source
end ConnesWeilRH
