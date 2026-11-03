import ConnesWeilRH.Dev.C1RouteARationalTightCell3298
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithCellLocalJets3225

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem intervalIntegral_record2680_40960_tight_aggregate_upper3299 :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 ratCellValueUpperTight3298
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_aggregate_upper_with_cell_local_jets3225
  intro index hindex
  exact ratCellValueUpperTight3298_spec hindex

end ConnesWeilRH.Dev
