/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramMomentModel

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramMomentModel

open C1ClassGramScale
open C1ClassGramMomentReduction

#print axioms classGramMomentModel
#print axioms classMoment_even_recurrence_instances
#print axioms classGramUnitMatrix_eq_classGramMomentModel

example : classGramUnitMatrix =
    classGramMomentModel (classMoment 0) (classMoment 2) :=
  classGramUnitMatrix_eq_classGramMomentModel

end C1ClassGramMomentModel
end Source
end ConnesWeilRH
