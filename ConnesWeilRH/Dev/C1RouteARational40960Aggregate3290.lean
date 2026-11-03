import ConnesWeilRH.Dev.C1RouteARationalCellFamily3288
import ConnesWeilRH.Dev.C1RouteARationalCellWeight3289
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithCellLocalJets3225

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def ratCellValueUpper3289 (index : ℕ) : ℝ :=
  ratCellValueUpper3277 (ratCellWeightInterval3289 index)
    (RatRect3276.sumFinset (ratCellFamilyRect3288 index) Finset.univ)

theorem ratCellWeight3289_spec
    {index : ℕ} (hindex : index < 40960) :
    (ratCellWeightInterval3289 index).Mem
      (Real.exp (-(1 / 2 : ℝ) * record2680Center3212 index)) := by
  exact ratCellWeightInterval_mem3289 hindex

theorem ratCellFamilyRect3288_spec
    {index : ℕ} (hindex : index < 40960) (family : Fin 30) :
    (ratCellFamilyRect3288 index family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 index)) := by
  exact ratCanonicalFamilyRect_mem3288 hindex family

theorem record2680_40960_midpoint_upper3289
    {index : ℕ} (hindex : index < 40960) :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 index) ≤
      ratCellValueUpper3289 index := by
  unfold ratCellValueUpper3289
  apply ratCellValueUpper3277_family_spec
  · convert ratCellWeight3289_spec hindex using 1 <;> ring
  · intro family
    exact ratCellFamilyRect3288_spec hindex family

theorem intervalIntegral_record2680_40960_rational_aggregate_upper3290 :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 position) ≤
      Finset.sum (Finset.range 40960)
        (record2680CellUpper3209 record2680Grid3212 ratCellValueUpper3289
          record2680CellSecondBound3224 record2680CellFourthBound3224
          record2680UniformSixthBound3220) := by
  apply intervalIntegral_record2680_40960_aggregate_upper_with_cell_local_jets3225
  intro index hindex
  exact record2680_40960_midpoint_upper3289 hindex

end ConnesWeilRH.Dev
