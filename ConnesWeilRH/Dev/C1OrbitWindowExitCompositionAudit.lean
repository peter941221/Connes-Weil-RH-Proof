/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1OrbitWindowExitComposition

/-!
# Audit for `C1OrbitWindowExitComposition` (record 1099)

Pins the axiom profile of every declaration of the C3 exit-composition
module.  The expected axiom base is exactly
`[propext, Classical.choice, Quot.sound]` and `sorryAx` must be absent.
-/

namespace ConnesWeilRH.Source.C1OrbitWindowExitCompositionAudit

open ConnesWeilRH.Source
open ConnesWeilRH.Source.C1OrbitWindowExitComposition

-- public surface
#check @qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate
#check @sourceRH_of_orbitWindowSemiLocalGate

-- axiom pins
#print axioms qw_nonneg_of_healthyDetectorData_of_orbitWindowSemiLocalGate
#print axioms sourceRH_of_orbitWindowSemiLocalGate

end ConnesWeilRH.Source.C1OrbitWindowExitCompositionAudit
