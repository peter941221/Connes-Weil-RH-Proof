/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1G8MasterExit

/-!
# Audit for C1G8MasterExit

Audits all master exits in `ConnesWeilRH.Dev.C1G8MasterExit`:
- `#check` declarations
- `#print axioms` verifying that each declaration depends strictly on the three standard
  axioms: `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8MasterExitAudit

open ConnesWeilRH.Source.C1G8MasterExit

#check @sourceRH_of_right_g8SameOwnerReadbackData
#print axioms sourceRH_of_right_g8SameOwnerReadbackData

#check @riemannHypothesis_of_right_g8SameOwnerReadbackData
#print axioms riemannHypothesis_of_right_g8SameOwnerReadbackData

#check @riemannHypothesis_of_right_survivorCore_and_aggregateEq
#print axioms riemannHypothesis_of_right_survivorCore_and_aggregateEq

#check @riemannHypothesis_of_right_annular_wing_majorant_and_aggregateEq
#print axioms riemannHypothesis_of_right_annular_wing_majorant_and_aggregateEq

end C1G8MasterExitAudit
end Source
end ConnesWeilRH
