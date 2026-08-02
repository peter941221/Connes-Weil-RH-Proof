/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistoryMetricGuard

/-!
# Import-facing audit for the completed physical-history metric guard
-/

namespace ConnesWeilRH.Dev.CCM24FiniteSCompletedPhysicalHistoryMetricGuardAudit

open ConnesWeilRH.Source
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedPhysicalHistoryMetricGuard

#check @metricHistoryReadout_eq_forwardEndpoint_iff_forward_zero
#check @metricHistoryReadout_ne_forwardEndpoint_of_forward_ne_zero

#print axioms metricHistoryReadout_eq_forwardEndpoint_iff_forward_zero
#print axioms metricHistoryReadout_ne_forwardEndpoint_of_forward_ne_zero

end ConnesWeilRH.Dev.CCM24FiniteSCompletedPhysicalHistoryMetricGuardAudit
