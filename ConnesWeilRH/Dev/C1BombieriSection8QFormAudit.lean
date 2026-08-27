/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8QForm

/-!
# Audit for the Q-form readback leaf

Focused axiom prints for the public declarations of the slice-12a
leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8QFormAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8QForm.dcoef
#print axioms ConnesWeilRH.Source.C1BombieriSection8QForm.continuous_expSum
#print axioms ConnesWeilRH.Source.C1BombieriSection8QForm.dcoef_mul_conj
#print axioms ConnesWeilRH.Source.C1BombieriSection8QForm.expSum_qForm
#print axioms ConnesWeilRH.Source.C1BombieriSection8QForm.expSum_qIntegrand_mass

end C1BombieriSection8QFormAudit
end Source
end ConnesWeilRH
