/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8KernelWeights

/-!
# Audit: weighted Bombieri kernel entries

Every public declaration of
`ConnesWeilRH.Dev.C1BombieriSection8KernelWeights` must depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8KernelWeightsAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8KernelWeights.winInt_neg
#print axioms ConnesWeilRH.Source.C1BombieriSection8KernelWeights.weighted_twoT_bombieriKstar

end C1BombieriSection8KernelWeightsAudit
end Source
end ConnesWeilRH
