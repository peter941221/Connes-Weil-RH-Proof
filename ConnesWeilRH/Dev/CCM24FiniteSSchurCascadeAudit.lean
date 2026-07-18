/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurCascade

namespace ConnesWeilRH.Dev.CCM24FiniteSSchurCascadeAudit

open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurCascade

#print axioms detectorIntertwiningDefect_eq_boundary
#print axioms transitionCoDefect_eq_ambient_add_boundary
#print axioms intertwiningDefect_mul
#print axioms rawFrame_gram_eq_inverseGram
#print axioms gramInverse_mul_numerator_eq_ordered
#print axioms inverseDefect_eq_inverseGrowth
#print axioms conjugated_inverseDefect_eq_delta_sub

end ConnesWeilRH.Dev.CCM24FiniteSSchurCascadeAudit
