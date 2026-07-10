/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20Concrete

/-!
# Plan 016 M2/M4 import audit

This audit fixes the axiom boundary of the ordinary positive-trace theorem and
the finite conditioning-space theorem for compact remainders.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsM2M4Audit

open Source.CC20Concrete

#check PositiveTrace.BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong
#check PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition
#check PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
#check CompactBadSpace.exists_finiteDimensional_controlSpace
#check CompactBadSpace.exists_finiteDimensional_remainder_nonpositive

#print axioms PositiveTrace.BasisHilbertSchmidtData.positiveComposition_isTraceClassAlong
#print axioms PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition
#print axioms PositiveTrace.BasisHilbertSchmidtData.ordinaryTrace_positiveComposition_re_nonnegative
#print axioms CompactBadSpace.exists_finiteDimensional_controlSpace
#print axioms CompactBadSpace.exists_finiteDimensional_remainder_nonpositive

end UnifiedRemainingGapsM2M4Audit
end Dev
end ConnesWeilRH
