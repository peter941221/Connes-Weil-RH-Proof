/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperAssembly

/-!
# C1WindowTaperAssemblyAudit - axiom audit for the component 4 Young assembly leaf

Every declaration of `C1WindowTaperAssembly` must print exactly
`[propext, Classical.choice, Quot.sound]`: no `sorryAx`, and no analytic
black-box axiom may enter the Young/convolution same-owner budget chain.
-/

open ConnesWeilRH.Source.C1WindowTaperAssembly

#print axioms compactLogL1
#print axioms compactLogL2sq_nonneg
#print axioms compactLogL1_nonneg
#print axioms integral_weighted_cauchySchwarz
#print axioms young_kernel_sq_le
#print axioms compactLogL1_sq_le_of_window
#print axioms compactLogL2sq_convolution_le
#print axioms compactLogL2sq_convolution_le_of_window
#print axioms exists_assembledOwner_cost_le
