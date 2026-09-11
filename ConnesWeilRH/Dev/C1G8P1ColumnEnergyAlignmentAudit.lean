/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1ColumnEnergyAlignment

/-!
# Audit for the G8 P1 column energy alignment

Every owner declaration must print exactly `[propext, Classical.choice,
Quot.sound]`.

Verification batch: `1540_g8_p1_column_energy_alignment_batch.log`.
-/

#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.summable_comp_normSq_of_contractive_pull
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.summable_metricBoundaryComposite_normSq_of_fullCarrierColumnEnergy
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.norm_radialSoninBoundaryCrossing_apply_oldSuffixFrame_le
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.summable_radialCrossingAfterOldFrame_normSq_of_fullCarrierColumnEnergy
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.metricBoundaryColumnEnergyOperator
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.metricBoundaryCauchyPairData
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.metricBoundaryCauchyPairData_traceProduct_eq_energyOperator
#print axioms ConnesWeilRH.Source.C1G8P1ColumnEnergyAlignment.metricBoundaryColumnEnergyOperator_isTraceClassAlong
