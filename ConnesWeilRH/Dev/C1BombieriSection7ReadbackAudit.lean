/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Readback

/-!
# Audit for the Bombieri section-7 kernel readback

Focused axiom prints for every declaration in the readback leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7ReadbackAudit

open ConnesWeilRH.Source.C1BombieriSection7Readback

#print axioms ConnesWeilRH.Source.C1BombieriSection7Readback.bombieriK
#print axioms ConnesWeilRH.Source.C1BombieriSection7Readback.bombieriKstar
#print axioms ConnesWeilRH.Source.C1BombieriSection7Readback.bombieriK_zero
#print axioms ConnesWeilRH.Source.C1BombieriSection7Readback.bombieriK_re_add_mulI

end C1BombieriSection7ReadbackAudit
end Source
end ConnesWeilRH
