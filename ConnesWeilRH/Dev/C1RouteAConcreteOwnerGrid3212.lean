import ConnesWeilRH.Dev.C1RouteAConcreteOwnerGlobalAggregateUpper3211

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Grid3212 (index : ℕ) : ℝ :=
  -diagnosticRadius3201 + (index : ℝ) *
    (2 * diagnosticRadius3201 / 40960)

noncomputable def record2680Center3212 (index : ℕ) : ℝ :=
  (record2680Grid3212 index + record2680Grid3212 (index + 1)) / 2

theorem record2680_grid_left3212 :
    record2680Grid3212 0 = -diagnosticRadius3201 := by
  norm_num [record2680Grid3212]

theorem record2680_grid_right3212 :
    record2680Grid3212 40960 = diagnosticRadius3201 := by
  norm_num [record2680Grid3212]
  ring

theorem record2680_grid_order3212 {index : ℕ} (hindex : index < 40960) :
    record2680Grid3212 index < record2680Grid3212 (index + 1) := by
  unfold record2680Grid3212
  have hradius : 0 < diagnosticRadius3201 := by
    norm_num [diagnosticRadius3201]
  have hstep : 0 < 2 * diagnosticRadius3201 / 40960 := by
    positivity
  have hindex_real : (index : ℝ) < ((index + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self index
  nlinarith

theorem record2680_center_midpoint3212 (index : ℕ) :
    record2680Center3212 index =
      (record2680Grid3212 index + record2680Grid3212 (index + 1)) / 2 := by
  rfl

end ConnesWeilRH.Dev
