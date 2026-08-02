/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGateTraceAnalyticWindowIdentityBridge

namespace ConnesWeilRH.Dev.CCM24FiniteSGateTraceAnalyticWindowIdentityBridgeAudit

open ConnesWeilRH.Source.CCM25Concrete
open CCM24FiniteSGateTraceAnalyticWindowIdentityBridge

private abbrev TraceBoundFromOriginalMultiplierIdInput :=
  lowerFactorGauged_trace_norm_le_of_analytic_window_originalMultiplier_idInput

#check @TraceBoundFromOriginalMultiplierIdInput

#print axioms TraceBoundFromOriginalMultiplierIdInput

end ConnesWeilRH.Dev.CCM24FiniteSGateTraceAnalyticWindowIdentityBridgeAudit
