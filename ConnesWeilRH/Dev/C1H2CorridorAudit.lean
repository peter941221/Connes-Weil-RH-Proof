/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1H2Corridor

/-!
# C1H2CorridorAudit - axiom prints for the H2 corridor leaf
Build preregistration: docs/proofs/1367_h2_corridor_formalization_design.md s4;
three standard axioms, zero sorryAx.
-/

#print axioms ConnesWeilRH.Source.C1H2Corridor.fstar_one
#print axioms ConnesWeilRH.Source.C1H2Corridor.noMajority_eps_mono
#print axioms ConnesWeilRH.Source.C1H2Corridor.noMajority_height_mono
#print axioms ConnesWeilRH.Source.C1H2Corridor.qw_nonneg_of_windowMassBalance
#print axioms ConnesWeilRH.Source.C1H2Corridor.sourceRH_of_windowMassBalanceBridge
#print axioms ConnesWeilRH.Source.C1H2Corridor.sourceRH_of_countBridge
#print axioms ConnesWeilRH.Source.C1H2Corridor.sourceRH_of_A2Bridge
#print axioms ConnesWeilRH.Source.C1H2Corridor.sourceRH_windowMassBalance
