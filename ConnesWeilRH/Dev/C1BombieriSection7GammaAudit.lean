/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Gamma

/-!
# Audit for the finite-Γ (7.2)/(7.4)/(7.5) matrix leaf

Focused axiom prints for every public declaration of the Gamma leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7GammaAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriWOfZ
#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriHMatrix
#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriHMatrix_transpose
#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriHMatrix_mulVec_weight
#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriEigenvec_iff
#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriD
#print axioms ConnesWeilRH.Source.C1BombieriSection7Gamma.bombieriD_zero

end C1BombieriSection7GammaAudit
end Source
end ConnesWeilRH
