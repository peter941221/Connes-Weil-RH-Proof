import ConnesWeilRH.Dev.C1RouteAConcreteOwnerGrid3212
import ConnesWeilRH.Dev.C1RouteAOwnerWindowZeroExtension3201

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2680_first_center_inside_ownerRadius3215 :
    |record2680Center3212 0| < storedWidth 4 ^ 2 := by
  rw [record2680Center3212, record2680Grid3212, record2680Grid3212,
    diagnosticRadius3201]
  have hwidth : storedWidth 4 = (1441151880758559 / 562949953421312 : ℝ) := by
    change (1441151880758559 / 562949953421312 : ℝ) =
      1441151880758559 / 562949953421312
    rfl
  rw [hwidth]
  norm_num [abs_of_neg]

theorem record2680_first_center_not_support_zero3215 :
    ¬ |record2680Center3212 0| ≥ storedWidth 4 ^ 2 := by
  exact not_le_of_gt record2680_first_center_inside_ownerRadius3215

end ConnesWeilRH.Dev
