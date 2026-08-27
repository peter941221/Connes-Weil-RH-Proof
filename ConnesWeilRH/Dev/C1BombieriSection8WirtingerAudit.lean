/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8Wirtinger

/-!
# Audit for the Wirtinger IBP-core leaf

Focused axiom prints for the public declarations of the (8.13) first-slice
leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8Wirtinger.phiEven
#print axioms ConnesWeilRH.Source.C1BombieriSection8Wirtinger.hasDerivAt_phiEven
#print axioms ConnesWeilRH.Source.C1BombieriSection8Wirtinger.phiEven_ode
#print axioms ConnesWeilRH.Source.C1BombieriSection8Wirtinger.hasDerivAt_cast
#print axioms ConnesWeilRH.Source.C1BombieriSection8Wirtinger.hasDerivAt_g_mul_phiEven'
#print axioms ConnesWeilRH.Source.C1BombieriSection8Wirtinger.ibpCoreEven

end C1BombieriSection8WirtingerAudit
end Source
end ConnesWeilRH
