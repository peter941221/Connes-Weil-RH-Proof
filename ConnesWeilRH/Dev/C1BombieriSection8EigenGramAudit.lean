/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8EigenGram

/-!
# Audit: the eigen-Gram transport leaf

Every public declaration of
`ConnesWeilRH.Dev.C1BombieriSection8EigenGram` must depend only on
`[propext, Classical.choice, Quot.sound]` — zero `sorryAx`, zero
additional axioms.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8EigenGramAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8EigenGram.conj_bombieriWOfZ
#print axioms ConnesWeilRH.Source.C1BombieriSection8EigenGram.mulVec_weight_apply
#print axioms ConnesWeilRH.Source.C1BombieriSection8EigenGram.bombieriEigen_gram

end C1BombieriSection8EigenGramAudit
end Source
end ConnesWeilRH
