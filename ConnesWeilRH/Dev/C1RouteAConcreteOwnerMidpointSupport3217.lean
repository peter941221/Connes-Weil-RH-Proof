import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerBoundaryGeometry3215

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem externalFamilyValue2344_re_eq_bump_cos_sin3217
    (coefficient : ℂ) (modulation radius position : ℝ) :
    (externalFamilyValue2344 coefficient modulation radius position).re =
      coefficient.re * widthBump radius position * Real.cos (modulation * position) -
        coefficient.im * widthBump radius position * Real.sin (modulation * position) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, expMulIre2676, expMulIim2676]
  ring

/- Cell 0 is inside family 4 only. This isolates the remaining signed midpoint
   obligation from the 30-family aggregate. -/

theorem record2680_first_center_only_family4_3217 :
    externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 0) =
      externalFamilyValue2344 (record2680CorrectionCoefficient 4)
        (capturedModulations2584 4) (storedWidth 4 ^ 2)
        (record2680Center3212 0) := by
  unfold externalPhysical2344
  apply Finset.sum_eq_single (4 : Fin 30)
  · intro index _ hindex
    have houtside : ¬ |record2680Center3212 0| < storedWidth index ^ 2 := by
      fin_cases index <;>
        norm_num [record2680Center3212, record2680Grid3212,
          diagnosticRadius3201, storedWidth, Fin.ext_iff] at *
    simp only [externalFamilyValue2344, if_neg houtside]
  · simp

theorem record2680_first_center_family4_re_formula3217 :
    (externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 0)).re =
      (record2680CorrectionCoefficient 4).re *
          widthBump (storedWidth 4 ^ 2) (record2680Center3212 0) *
          Real.cos (capturedModulations2584 4 * record2680Center3212 0) -
        (record2680CorrectionCoefficient 4).im *
          widthBump (storedWidth 4 ^ 2) (record2680Center3212 0) *
          Real.sin (capturedModulations2584 4 * record2680Center3212 0) := by
  rw [record2680_first_center_only_family4_3217]
  exact externalFamilyValue2344_re_eq_bump_cos_sin3217 _ _ _ _

end ConnesWeilRH.Dev
