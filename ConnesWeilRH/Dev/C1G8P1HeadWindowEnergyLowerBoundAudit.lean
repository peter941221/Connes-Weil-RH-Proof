/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1HeadWindowEnergyLowerBound

/-!
# Audit for the G8 P1 head-window energy lower bound (record 1330)

Verification batch: `1542_g8_p1_head_window_batch.log`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1HeadWindowEnergyLowerBoundAudit

open scoped InnerProduct InnerProductSpace

open ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound

#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.log_headWindowScale
#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.radialSupportProjection_coeFn_indicator
#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.radialComplement_coeFn_indicator
#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.radialComplement_translation_commute
#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.norm_radialComplement_headWindow_le_norm_antiresonantCore
#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.radialSupportProjection_newSuffixFrame
#print axioms ConnesWeilRH.Source.C1G8P1HeadWindowEnergyLowerBound.summable_headWindowCrossing_normSq_of_antiresonantColumnEnergy

end C1G8P1HeadWindowEnergyLowerBoundAudit
end Source
end ConnesWeilRH
