/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1LaneRStrictness

namespace ConnesWeilRH.Source.C1LaneRStrictness

open C1LaneRNarrowArch

#print axioms C1LaneRD3Root.tripleVanishingRoot_test_ne_zero_of_laplaceAt_two
#print axioms C1LaneRNarrowArch.archimedeanTerm_le_narrow_budget
#print axioms C1LaneRNarrowArch.archimedeanTerm_nonpos_of_narrow_budget
#print axioms C1LaneRNarrowArch.archimedeanTerm_neg_of_narrow_budget
#print axioms C1LaneRNarrowArch.narrowArchRadius_budget_lt
#print axioms narrowArchRoot_test_ne_zero
#print axioms narrowArchRoot_square_mass_pos
#print axioms narrowArchRoot_archimedeanTerm_neg
#print axioms narrowArchRoot_qw_pos

example : 0 < C1SameOwnerWeil.qw narrowArchRoot :=
  narrowArchRoot_qw_pos

end ConnesWeilRH.Source.C1LaneRStrictness
