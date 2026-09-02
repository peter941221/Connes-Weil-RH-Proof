/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate

/-!
# Audit for `C1OrbitWindowSemiLocalGate` (record 1089)

Pins the axiom profile of every declaration of the orbit-window semi-local
gate module.  The expected axiom base is exactly
`[propext, Classical.choice, Quot.sound]` and `sorryAx` must be absent.
-/

namespace ConnesWeilRH.Source.C1OrbitWindowSemiLocalGateAudit

open ConnesWeilRH.Source
open ConnesWeilRH.Source.C1OrbitWindowSemiLocalGate

-- public surface
#check @C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate
#check @C1OrbitWindowSemiLocalGate.qw_nonneg_of_orbitWindowSemiLocalGate
#check @C1OrbitWindowSemiLocalGate.log_lt_of_mem_globalPrimeIndexSet_of_support_subset
#check @C1OrbitWindowSemiLocalGate.mem_globalPrimeIndexSet_convolutionSquare_lt_exp
#check @C1OrbitWindowSemiLocalGate.exists_pinnedOrbitDetector_with_window_and_visiblePrimes

-- axiom pins
#print axioms C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate
#print axioms C1OrbitWindowSemiLocalGate.qw_nonneg_of_orbitWindowSemiLocalGate
#print axioms C1OrbitWindowSemiLocalGate.log_lt_of_mem_globalPrimeIndexSet_of_support_subset
#print axioms C1OrbitWindowSemiLocalGate.mem_globalPrimeIndexSet_convolutionSquare_lt_exp
#print axioms C1OrbitWindowSemiLocalGate.exists_pinnedOrbitDetector_with_window_and_visiblePrimes

end ConnesWeilRH.Source.C1OrbitWindowSemiLocalGateAudit
