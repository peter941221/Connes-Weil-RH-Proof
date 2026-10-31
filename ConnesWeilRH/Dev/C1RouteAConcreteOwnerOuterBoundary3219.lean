import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- The last diagnostic midpoint is still inside the selected owner's support.
   Its value_upper = 0 cannot be justified by support-zero. -/

theorem record2680_last_center_inside_ownerRadius3219 :
    |record2680Center3212 40959| < storedWidth 4 ^ 2 := by
  have hcenter : 0 < record2680Center3212 40959 := by
    norm_num [record2680Center3212, record2680Grid3212, diagnosticRadius3201]
  rw [abs_of_pos hcenter]
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero,
    record2680Center3212, record2680Grid3212, diagnosticRadius3201,
    storedWidth, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev