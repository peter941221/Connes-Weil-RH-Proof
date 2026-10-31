import ConnesWeilRH.Dev.C1RouteAConcreteOwnerUniformSixth3220

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680UniformDerivativeUpper3222 (order : ℕ) : ℝ :=
  ∑ index : Fin 30,
    weightedFamilyCellUpper2538 order (record2680CorrectionCoefficient index)
      (-1 / 2) (capturedModulations2584 index) (storedWidth index ^ 2)
      0 1 (-(storedWidth index ^ 2)) (storedWidth index ^ 2)

noncomputable def record2680UniformDerivativeBound3222 (order : ℕ) (_ : ℕ) : ℝ :=
  record2680UniformDerivativeUpper3222 order

theorem record2680_uniform_derivative_upper_nonneg3222
    (order : ℕ) (horder : order ≤ 6) :
    0 ≤ record2680UniformDerivativeUpper3222 order := by
  unfold record2680UniformDerivativeUpper3222
  apply Finset.sum_nonneg
  intro index _
  unfold weightedFamilyCellUpper2538
  have hsum : 0 ≤ ∑ index' ∈ Finset.range (order + 1),
      (Nat.choose order index' : ℝ) *
        ‖weightedLambda2537 (-1 / 2) (capturedModulations2584 index)‖ ^ index' *
        localCoupledBumpUpper2536 (order - index') (storedWidth index ^ 2) 0 1 := by
    apply Finset.sum_nonneg
    intro index' _
    exact mul_nonneg (by positivity)
      (localCoupledBumpUpper2536_nonneg _
        (pow_pos (storedWidth_pos index) 2) (by norm_num) (by norm_num) (by norm_num))
  exact mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) hsum)

theorem record2680_uniform_derivative_complex_bound3222
    (order : ℕ) (horder : order ≤ 6) (coordinate : ℝ) :
    ‖iteratedDeriv order
      (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate‖ ≤
      record2680UniformDerivativeUpper3222 order := by
  rw [weightedPhysical2539_iteratedDeriv]
  unfold record2680UniformDerivativeUpper3222
  calc
    ‖∑ index : Fin 30,
        record2680CorrectionCoefficient index *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584 index coordinate‖ ≤
        ∑ index : Fin 30, ‖record2680CorrectionCoefficient index *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584 index coordinate‖ := by
      simpa using (norm_sum_le (Finset.univ : Finset (Fin 30))
        (fun index => record2680CorrectionCoefficient index *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584 index coordinate))
    _ ≤ ∑ index : Fin 30,
        weightedFamilyCellUpper2538 order (record2680CorrectionCoefficient index)
          (-1 / 2) (capturedModulations2584 index) (storedWidth index ^ 2)
          0 1 (-(storedWidth index ^ 2)) (storedWidth index ^ 2) := by
      apply Finset.sum_le_sum
      intro index _
      by_cases hinside : |coordinate| < storedWidth index ^ 2
      · have hradius : 0 < storedWidth index ^ 2 :=
          pow_pos (storedWidth_pos index) 2
        have hratio_nonneg : 0 ≤ |coordinate / (storedWidth index ^ 2)| :=
          abs_nonneg _
        have hratio_le_one : |coordinate / (storedWidth index ^ 2)| ≤ 1 := by
          rw [abs_div, abs_of_pos hradius]
          exact (div_le_one hradius).mpr (le_of_lt hinside)
        have hposition : coordinate ∈
            Set.Icc (-(storedWidth index ^ 2)) (storedWidth index ^ 2) := by
          rw [Set.mem_Icc, ← abs_le]
          exact le_of_lt hinside
        have hbound := weightedExternalFamily_iteratedDeriv_le_cell2538 order horder
          (-1 / 2) (record2680CorrectionCoefficient index)
          (capturedModulations2584 index) hradius
          (by norm_num) (by norm_num) hratio_nonneg hratio_le_one hposition
        have heq : iteratedDeriv order
              (weightedFunction2348 (-1 / 2)
                (externalFamilyValue2344 (record2680CorrectionCoefficient index)
                  (capturedModulations2584 index) (storedWidth index ^ 2))) coordinate =
            record2680CorrectionCoefficient index *
              weightedUnitJet2539 order (-1 / 2) capturedModulations2584 index coordinate := by
          simpa [weightedUnitJet2539] using
            (weightedExternalFamily_coefficient_linear2539 order (-1 / 2)
              (record2680CorrectionCoefficient index)
              (capturedModulations2584 index) (position := coordinate) hradius)
        rw [← heq]
        exact hbound
      · have houtside : storedWidth index ^ 2 ≤ |coordinate| := not_lt.mp hinside
        have hradius : 0 < storedWidth index ^ 2 :=
          pow_pos (storedWidth_pos index) 2
        have hz := weightedExternalFamily_iteratedDeriv_zero_outside2538 order (-1 / 2)
          (record2680CorrectionCoefficient index) (capturedModulations2584 index)
          hradius houtside
        have heq : iteratedDeriv order
              (weightedFunction2348 (-1 / 2)
                (externalFamilyValue2344 (record2680CorrectionCoefficient index)
                  (capturedModulations2584 index) (storedWidth index ^ 2))) coordinate =
            record2680CorrectionCoefficient index *
              weightedUnitJet2539 order (-1 / 2) capturedModulations2584 index coordinate := by
          simpa [weightedUnitJet2539] using
            (weightedExternalFamily_coefficient_linear2539 order (-1 / 2)
              (record2680CorrectionCoefficient index)
              (capturedModulations2584 index) (position := coordinate) hradius)
        rw [← heq, hz, norm_zero]
        have hsum : 0 ≤ ∑ index' ∈ Finset.range (order + 1),
            (Nat.choose order index' : ℝ) *
              ‖weightedLambda2537 (-1 / 2) (capturedModulations2584 index)‖ ^ index' *
              localCoupledBumpUpper2536 (order - index') (storedWidth index ^ 2) 0 1 := by
          apply Finset.sum_nonneg
          intro index' _
          exact mul_nonneg (by positivity)
            (localCoupledBumpUpper2536_nonneg _ hradius (by norm_num) (by norm_num) (by norm_num))
        unfold weightedFamilyCellUpper2538
        exact mul_nonneg (norm_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) hsum)

theorem record2680_uniform_derivative_real_bound3222
    (order : ℕ) (horder : order ≤ 6) (coordinate : ℝ) :
    ‖iteratedDeriv order
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate‖ ≤
      record2680UniformDerivativeUpper3222 order := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584) order coordinate
    (weightedPhysical2539_contDiff (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)]
  have hre : ‖(iteratedDeriv order
      (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate).re‖ ≤
      ‖iteratedDeriv order
        (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ := by
    simpa only [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm
        (iteratedDeriv order
          (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
            capturedModulations2584) coordinate))
  exact hre.trans (record2680_uniform_derivative_complex_bound3222 order horder coordinate)

noncomputable def record2680UniformSecondBound3222 (index : ℕ) : ℝ :=
  record2680UniformDerivativeUpper3222 2

noncomputable def record2680UniformFourthBound3222 (index : ℕ) : ℝ :=
  record2680UniformDerivativeUpper3222 4

theorem record2680_uniform_second_bound3222
    {index : ℕ} (hindex : index < 40960) (coordinate : ℝ) :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate ≤
      record2680UniformSecondBound3222 index := by
  have hnorm := record2680_uniform_derivative_real_bound3222 2 (by norm_num) coordinate
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hnorm)

theorem record2680_uniform_fourth_bound3222
    {index : ℕ} (hindex : index < 40960) (coordinate : ℝ) :
    iteratedDeriv 4
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate ≤
      record2680UniformFourthBound3222 index := by
  have hnorm := record2680_uniform_derivative_real_bound3222 4 (by norm_num) coordinate
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hnorm)

theorem record2680_uniform_second_bound_nonneg3222 (index : ℕ) :
    0 ≤ record2680UniformSecondBound3222 index := by
  exact record2680_uniform_derivative_upper_nonneg3222 2 (by norm_num)

theorem record2680_uniform_fourth_bound_nonneg3222 (index : ℕ) :
    0 ≤ record2680UniformFourthBound3222 index := by
  exact record2680_uniform_derivative_upper_nonneg3222 4 (by norm_num)

end ConnesWeilRH.Dev
