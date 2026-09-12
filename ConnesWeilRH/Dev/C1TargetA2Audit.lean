/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1TargetA2

/-!
# C1TargetA2Audit - axiom prints for the counting-frame leaf
Build preregistration: docs/proofs/1365_targetA2_counting_frame_design.md s4;
three standard axioms, zero sorryAx.
-/

#print axioms ConnesWeilRH.Source.C1TargetA2.fstar_nonneg
#print axioms ConnesWeilRH.Source.C1TargetA2.fstar_zero
#print axioms ConnesWeilRH.Source.C1TargetA2.fstar_lt_one
#print axioms ConnesWeilRH.Source.C1TargetA2.fstar_mono
#print axioms ConnesWeilRH.Source.C1TargetA2.windowOnLineCount_le_total
#print axioms ConnesWeilRH.Source.C1TargetA2.windowNearLineOffCount_le_total
#print axioms ConnesWeilRH.Source.C1TargetA2.nearLineOffCount_eps_mono
#print axioms ConnesWeilRH.Source.C1TargetA2.sourceRH_windowNearLineOffCount_zero
#print axioms ConnesWeilRH.Source.C1TargetA2.sourceRH_targetA2_margin_reduction
