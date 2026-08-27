/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8BoundaryBridge

/-!
# Audit: the boundary-bridge leaf

Every public declaration of
`ConnesWeilRH.Dev.C1BombieriSection8BoundaryBridge` must depend only on
`[propext, Classical.choice, Quot.sound]` — zero `sorryAx`, zero
additional axioms.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8BoundaryBridgeAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8BoundaryBridge.conj_expI
#print axioms ConnesWeilRH.Source.C1BombieriSection8BoundaryBridge.negTwoSinI
#print axioms ConnesWeilRH.Source.C1BombieriSection8BoundaryBridge.mul_winInt_eq_sin
#print axioms ConnesWeilRH.Source.C1BombieriSection8BoundaryBridge.boundaryPair
#print axioms ConnesWeilRH.Source.C1BombieriSection8BoundaryBridge.gamma_sin_boundaryBridge

end C1BombieriSection8BoundaryBridgeAudit
end Source
end ConnesWeilRH
