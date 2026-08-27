/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Symmetry

/-!
# Audit for the full Bombieri symmetry law leaf

Focused axiom prints for every declaration in the symmetry-law leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7SymmetryAudit

open ConnesWeilRH.Source.C1BombieriSection7Symmetry

#print axioms ConnesWeilRH.Source.C1BombieriSection7Symmetry.bombieri7_core
#print axioms ConnesWeilRH.Source.C1BombieriSection7Symmetry.bombieriKstar_symmetryLaw
#print axioms ConnesWeilRH.Source.C1BombieriSection7Symmetry.bombieriKstar_symmetric

end C1BombieriSection7SymmetryAudit
end Source
end ConnesWeilRH
