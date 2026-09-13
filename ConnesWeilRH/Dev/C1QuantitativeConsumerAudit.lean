/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1QuantitativeConsumer

/-!
# C1QuantitativeConsumerAudit - axiom audit for the component 5 shape-layer consumer leaf

Every declaration of `C1QuantitativeConsumer` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom may enter the route-(A) margin consumption chain.  The two
open premises (`hfit`, `hJ1`) must remain hypotheses, not axiom-discharged
facts, and the record-1378 band bridge must remain a hypothesis of
`bandBridge_pos_of_margin_pos` / `exists_assembledOwner_bandBridge_pos`.
-/

open ConnesWeilRH.Source.C1QuantitativeConsumer

#print axioms margin_pos_of_cost_le_ceiling
#print axioms margin_pos_of_owner_cost_fits
#print axioms bandBridge_pos_of_margin_pos
#print axioms laplaceAt_assembled_eq_zero_of_target_eq_zero
#print axioms laplaceAt_assembled_ne_zero_of_target_ne_zero
#print axioms exists_assembledOwner_margin_pos
#print axioms exists_assembledOwner_bandBridge_pos
