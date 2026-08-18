/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1LaneRNarrowArch

namespace ConnesWeilRH.Source.C1LaneRNarrowArch

#print axioms narrowArchCoefficient_pos
#print axioms narrowArchRadius_pos
#print axioms narrowArchRadius_lt_one
#print axioms narrowArchRadius_log_inv
#print axioms narrowArchRadius_budget
#print axioms narrowArchBaseWidth_pos
#print axioms narrowArchRoot_square_support
#print axioms narrowArchRoot_square_support_subset_open_log_two
#print axioms narrowArchRoot_archimedeanTerm_nonpos
#print axioms narrowArchRoot_qw_eq_neg_archimedeanTerm
#print axioms narrowArchRoot_qw_nonneg

example : 0 ≤ C1SameOwnerWeil.qw narrowArchRoot :=
  narrowArchRoot_qw_nonneg

end ConnesWeilRH.Source.C1LaneRNarrowArch
