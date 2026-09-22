/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RouteAlphaOwner

/-!
# C1RouteAlphaOwnerAudit - axiom audit for the R1 route-alpha owner leaf

Every declaration of `C1RouteAlphaOwner` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom may enter the R1 assembly chain.  The archimedean gate `harch`
must remain a hypothesis of `healthyDetectorData_of_routeAlphaOwner` — the
open sign of records 1080/1081 is NOT discharged here — and `hfit`/`hJ1` must
remain hypotheses of `exists_routeAlphaOwner_margin_pos`, to be confirmed by
the record-1390 rig.
-/

open ConnesWeilRH.Source.C1RouteAlphaOwner

#print axioms routeAlphaNodes
#print axioms routeAlphaBaseValue
#print axioms healthyDetectorNodeTarget_norm_le_one
#print axioms routeAlphaIndex_card_le_four
#print axioms routeAlpha_target_card_norm_le_four
#print axioms routeAlphaRealPartBound_le_four_exp
#print axioms routeAlphaIndex_nonempty
#print axioms windowGramInverse_cost_re_nonneg
#print axioms exists_routeAlphaOwner
#print axioms exists_routeAlphaOwner_margin_pos
#print axioms healthyDetectorData_of_routeAlphaOwner
