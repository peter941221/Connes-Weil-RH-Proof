/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds

namespace ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBoundsAudit

open ConnesWeilRH.Source.CCM25Concrete
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBounds

#check @frameForwardCoframe_norm_le_one
#check @detectorLeg_norm_le
#check @forwardAdjointLeakage_norm_le
#check @forwardLeakage_norm_le

#print axioms frameForwardCoframe_norm_le_one
#print axioms detectorLeg_norm_le
#print axioms forwardAdjointLeakage_norm_le
#print axioms forwardLeakage_norm_le

end ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeResponseBoundsAudit
