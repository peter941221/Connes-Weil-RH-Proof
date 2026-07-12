/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20Concrete.CompactBadSpace

/-!
# Compact bad-space evaluation-span audit
-/

namespace ConnesWeilRH.Dev.CompactBadSpaceEvaluationAudit

open Source.CC20Concrete.CompactBadSpace

#check @mem_controlSpace_orthogonal_of_le_evaluationSpace
#check @exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace

#print mem_controlSpace_orthogonal_of_le_evaluationSpace
#print exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace

#print axioms mem_controlSpace_orthogonal_of_le_evaluationSpace
#print axioms exists_finiteDimensional_remainder_nonpositive_on_evaluationSpace

end ConnesWeilRH.Dev.CompactBadSpaceEvaluationAudit
