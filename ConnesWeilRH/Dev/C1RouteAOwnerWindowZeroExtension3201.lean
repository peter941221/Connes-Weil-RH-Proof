import ConnesWeilRH.Dev.C1RouteAExternalOwnerIdentity

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def diagnosticRadius3201 : ℝ := 65536001 / 10000000

theorem ownerRadius_lt_diagnosticRadius3201 :
    storedWidth 4 ^ 2 < diagnosticRadius3201 := by
  change (1441151880758559 / 562949953421312 : ℝ) ^ 2 < 65536001 / 10000000
  norm_num

theorem correctedPhysical_eq_zero_of_abs_ge_ownerRadius3201
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    {position : ℝ} (hposition : storedWidth 4 ^ 2 ≤ |position|) :
    correctedPhysical coefficients modulations position = 0 := by
  unfold correctedPhysical physicalFamilySum
  apply Finset.sum_eq_zero
  intro index _
  have hsupport : storedWidth index ^ 2 ≤ storedWidth 4 ^ 2 := by
    by_cases hindex : index = 4
    · simpa [hindex]
    · exact (other_squared_width_le_six index hindex).trans
        (le_of_lt fourth_squared_width_gt_six)
  have houtside : ¬ |position| < storedWidth index ^ 2 := by
    exact not_lt_of_ge (hsupport.trans hposition)
  simp only [widthBump, if_neg houtside, Complex.ofReal_zero, mul_zero, zero_mul]

theorem externalPhysical_eq_zero_of_abs_ge_ownerRadius3201
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    {position : ℝ} (hposition : storedWidth 4 ^ 2 ≤ |position|) :
    externalPhysical2344 coefficients modulations position = 0 := by
  rw [externalPhysical2344_eq_correctedPhysical]
  exact correctedPhysical_eq_zero_of_abs_ge_ownerRadius3201 coefficients modulations hposition

theorem externalPhysical_eq_zero_on_diagnostic_outer3201
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    {position : ℝ} (hposition : storedWidth 4 ^ 2 ≤ |position|) :
    |position| ≤ diagnosticRadius3201 →
      externalPhysical2344 coefficients modulations position = 0 := by
  intro _
  exact externalPhysical_eq_zero_of_abs_ge_ownerRadius3201 coefficients modulations hposition


noncomputable def weightedExternal3201 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (position : ℝ) : ℝ :=
  (Real.exp (sigma * position) *
    (externalPhysical2344 coefficients modulations position).re)

theorem intervalIntegral_weightedExternal_eq_zero_of_ownerOutside3201
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    {left right : ℝ}
    (houtside : ∀ position ∈ Set.uIcc left right,
      storedWidth 4 ^ 2 ≤ |position|) :
    (∫ position in left..right,
      weightedExternal3201 sigma coefficients modulations position) = 0 := by
  rw [intervalIntegral.integral_congr]
  · exact intervalIntegral.integral_zero
  · intro position hposition
    have hphysical := externalPhysical_eq_zero_of_abs_ge_ownerRadius3201
      coefficients modulations (houtside position hposition)
    simp only [weightedExternal3201, hphysical, mul_zero, Complex.zero_re,
      Real.exp_zero]

theorem diagnostic_outer_right_ownerOutside3201
    {position : ℝ} (hposition : position ∈
      Set.uIcc (storedWidth 4 ^ 2) diagnosticRadius3201) :
    storedWidth 4 ^ 2 ≤ |position| := by
  have hradius : storedWidth 4 ^ 2 ≤ diagnosticRadius3201 :=
    le_of_lt ownerRadius_lt_diagnosticRadius3201
  rw [Set.uIcc_of_le hradius] at hposition
  have hnonneg : 0 ≤ storedWidth 4 ^ 2 := by
    change (0 : ℝ) ≤ (1441151880758559 / 562949953421312 : ℝ) ^ 2
    positivity
  have hposition_nonneg : 0 ≤ position := hnonneg.trans hposition.1
  rw [abs_of_nonneg hposition_nonneg]
  exact hposition.1

theorem diagnostic_outer_left_ownerOutside3201
    {position : ℝ} (hposition : position ∈
      Set.uIcc (-diagnosticRadius3201) (-(storedWidth 4 ^ 2))) :
    storedWidth 4 ^ 2 ≤ |position| := by
  have hradius : -(diagnosticRadius3201 : ℝ) ≤ -(storedWidth 4 ^ 2) := by
    exact neg_le_neg (le_of_lt ownerRadius_lt_diagnosticRadius3201)
  rw [Set.uIcc_of_le hradius] at hposition
  have hnonneg : 0 ≤ storedWidth 4 ^ 2 := by
    change (0 : ℝ) ≤ (1441151880758559 / 562949953421312 : ℝ) ^ 2
    positivity
  have hposition_nonpos : position ≤ 0 := by
    exact le_trans hposition.2 (neg_nonpos.mpr hnonneg)
  rw [abs_of_nonpos hposition_nonpos]
  linarith [hposition.2]

theorem intervalIntegral_weightedExternal_zero_on_diagnostic_right3201
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    (∫ position in (storedWidth 4 ^ 2)..diagnosticRadius3201,
      weightedExternal3201 sigma coefficients modulations position) = 0 := by
  apply intervalIntegral_weightedExternal_eq_zero_of_ownerOutside3201
  intro position hposition
  exact diagnostic_outer_right_ownerOutside3201 hposition

theorem intervalIntegral_weightedExternal_zero_on_diagnostic_left3201
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    (∫ position in (-diagnosticRadius3201)..(-(storedWidth 4 ^ 2)),
      weightedExternal3201 sigma coefficients modulations position) = 0 := by
  apply intervalIntegral_weightedExternal_eq_zero_of_ownerOutside3201
  intro position hposition
  exact diagnostic_outer_left_ownerOutside3201 hposition
end ConnesWeilRH.Dev