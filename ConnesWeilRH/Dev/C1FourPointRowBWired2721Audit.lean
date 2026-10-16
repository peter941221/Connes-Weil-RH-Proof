/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointRowBWired2721

/-!
# Audit for record 2721 wired row-B module

Axiom census for the five public declarations of
`C1FourPointRowBWired2721` (2721B trio plus the 2721C discharge and
variant): each must depend on exactly the standard
trio `[propext, Classical.choice, Quot.sound]` and on no `sorryAx`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointRowBWired2721Audit

open ConnesWeilRH.Source.C1FourPointRowBWired2721

#print axioms wiredHsmallTailRowB2721
#print axioms wiredEtaBudgetRowB2721
#print axioms fourPointContradictionRowBWired2721
#print axioms wiredMultCapDischargedRowB2721C
#print axioms fourPointContradictionRowBWired2721C

end C1FourPointRowBWired2721Audit
end Source
end ConnesWeilRH
