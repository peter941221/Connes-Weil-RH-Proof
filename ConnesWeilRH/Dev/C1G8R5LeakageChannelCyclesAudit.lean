/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R5LeakageChannelCycles

/-!
# Axiom audit for the leakage-channel cycles leaf

Every cycle is pure `ordinaryTraceAlong_traceProduct_eq_cyclic` bookkeeping
plus the record 1569 split, so the expected footprint is exactly the standard
trio `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms ConnesWeilRH.Dev.ordinaryTraceAlong_g8R5LeakageResponseChannel_eq_cyclic
#print axioms ConnesWeilRH.Dev.ordinaryTraceAlong_g8R5LeakageTotalChannel_eq_cyclic
#print axioms ConnesWeilRH.Dev.ordinaryTraceAlong_g8R5LeakageRemainderChannel_eq_cyclic_pairSum
