/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7H

/-!
# Audit for the (7.3) normalized-kernel leaf

Focused axiom prints for the public declarations of the `H` leaf (the
two weight helpers are `private` and audited through their consumers).
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7HAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection7H.bombieriH
#print axioms ConnesWeilRH.Source.C1BombieriSection7H.bombieriH_mul_weight_eq
#print axioms ConnesWeilRH.Source.C1BombieriSection7H.bombieriH_symmetric

end C1BombieriSection7HAudit
end Source
end ConnesWeilRH
