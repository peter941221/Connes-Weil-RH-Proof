/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.SoninWindowTransport

/-!
Audit for `SoninWindowTransport.lean`: print the statements and the axiom
footprint of every declaration.
-/

open ConnesWeilRH.Dev.SoninWindowTransport

#check @IsWindowWitness
#check @mem_radialSupport_of_window
#print axioms mem_radialSupport_of_window
#check @mem_fourierSupport_of_window
#print axioms mem_fourierSupport_of_window
#check @carrier_nontrivial_of_window_witness
#print axioms carrier_nontrivial_of_window_witness
