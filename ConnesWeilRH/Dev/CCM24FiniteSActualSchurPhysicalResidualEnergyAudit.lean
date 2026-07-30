/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurPhysicalResidualEnergy

namespace ConnesWeilRH.Dev.CCM24FiniteSActualSchurPhysicalResidualEnergyAudit

open ConnesWeilRH.Source.CCM25Concrete
open CCM24FiniteSActualSchurPhysicalResidualEnergy

#check @tsum_normSq_postcomp_residual_le
#check @sourceActualBandForwardTransportResidual_tsum_normSq_postcomp_le

#print axioms tsum_normSq_postcomp_residual_le
#print axioms sourceActualBandForwardTransportResidual_tsum_normSq_postcomp_le

end ConnesWeilRH.Dev.CCM24FiniteSActualSchurPhysicalResidualEnergyAudit
