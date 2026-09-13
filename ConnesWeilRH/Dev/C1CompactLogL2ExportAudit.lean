/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1CompactLogL2Export

/-!
# Audit for C1CompactLogL2Export

Axiom prints for every declaration; acceptance requires each list to be a
subset of `[propext, Classical.choice, Quot.sound]` with zero `sorryAx`.
-/

#print axioms ConnesWeilRH.Source.C1CompactLogL2Export.compactLogL2sq
#print axioms ConnesWeilRH.Source.C1CompactLogL2Export.intervalIntegral_cauchySchwarz
#print axioms ConnesWeilRH.Source.C1CompactLogL2Export.laplaceAt_sq_le
