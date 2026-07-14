/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogControlFrame

/-!
# Import-facing audit for Haar/log dense control transport
-/

namespace ConnesWeilRH.Dev.GlobalLogControlFrameAudit

open Source.CC20Concrete

#check @dense_span_cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
#check @exists_finite_cc20WindowHaarRegularRemainder_nonpositive_on_logBasis_rows

#print dense_span_cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
#print exists_finite_cc20WindowHaarRegularRemainder_nonpositive_on_logBasis_rows

#print axioms dense_span_cc20GlobalLogWindowRestrictedL2HaarPreimageBasis
#print axioms exists_finite_cc20WindowHaarRegularRemainder_nonpositive_on_logBasis_rows

end ConnesWeilRH.Dev.GlobalLogControlFrameAudit
