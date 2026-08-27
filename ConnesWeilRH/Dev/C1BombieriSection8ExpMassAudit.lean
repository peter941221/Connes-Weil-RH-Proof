/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8ExpMass

/-!
# Audit for the (8.5) exponential-sum leaf

Focused axiom prints for the public declarations of the exponential-sum
slice.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8ExpMassAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.conj_mul_d
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.conj_expTerm
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.conj_term_mul
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.castSumExpI
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.expPair_mul
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.gramPair
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.hasDerivAt_expTerm
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.hasDerivAt_expSum
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.winInt
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.integral_winInt
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpMass.expSum_mass_integral

end C1BombieriSection8ExpMassAudit
end Source
end ConnesWeilRH
