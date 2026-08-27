/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7DiagSymmetry

/-!
# Audit for the diagonal slice of the Bombieri symmetry law

Focused axiom prints for every declaration in the diagonal-slice leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7DiagSymmetryAudit

open ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry

#print axioms ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry.bombieriK_diagPair
#print axioms ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry.bombieriKstar_diagonalFold
#print axioms ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry.bombieriKstar_diagonalClosedForm
#print axioms ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry.bombieriK_genPair

end C1BombieriSection7DiagSymmetryAudit
end Source
end ConnesWeilRH
