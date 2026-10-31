import ConnesWeilRH.Dev.C1RouteAConcreteOwnerAggregateWithUniformJets3223

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680CellDerivativeUpper3224 (order index : ℕ) : ℝ :=
  ∑ family : Fin 30,
    if cellNearAbs2538 (record2680Grid3212 index)
        (record2680Grid3212 (index + 1)) < storedWidth family ^ 2 then
      weightedFamilyCellUpper2538 order (record2680CorrectionCoefficient family)
        (-1 / 2) (capturedModulations2584 family) (storedWidth family ^ 2)
        (cellNearAbs2538 (record2680Grid3212 index)
          (record2680Grid3212 (index + 1)) / (storedWidth family ^ 2))
        (min (max |record2680Grid3212 index|
          |record2680Grid3212 (index + 1)|) (storedWidth family ^ 2) /
          (storedWidth family ^ 2))
        (record2680Grid3212 index) (record2680Grid3212 (index + 1))
    else 0

theorem weightedFamilyCellUpper2538_nonneg3224
    (order : ℕ) (coefficient : ℂ) (sigma modulation radius near far a b : ℝ)
    (hradius : 0 < radius) (hnear : 0 ≤ near) (hnear_one : near < 1)
    (hfar : 0 ≤ far) :
    0 ≤ weightedFamilyCellUpper2538 order coefficient sigma modulation radius
      near far a b := by
  unfold weightedFamilyCellUpper2538
  have hsum : 0 ≤ ∑ index ∈ Finset.range (order + 1),
      (Nat.choose order index : ℝ) * ‖weightedLambda2537 sigma modulation‖ ^ index *
        localCoupledBumpUpper2536 (order - index) radius near far := by
    apply Finset.sum_nonneg
    intro index _
    exact mul_nonneg (by positivity)
      (localCoupledBumpUpper2536_nonneg _ hradius hnear hnear_one hfar)
  exact mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) hsum)

theorem record2680_cell_derivative_complex_bound3224
    (order : ℕ) (horder : order ≤ 6) {index : ℕ} (hindex : index < 40960) :
    ‖iteratedDeriv order
      (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 index)‖ ≤
      record2680CellDerivativeUpper3224 order index := by
  rw [weightedPhysical2539_iteratedDeriv]
  unfold record2680CellDerivativeUpper3224
  calc
    ‖∑ family : Fin 30,
        record2680CorrectionCoefficient family *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584 family
            (record2680Center3212 index)‖ ≤
        ∑ family : Fin 30, ‖record2680CorrectionCoefficient family *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584 family
            (record2680Center3212 index)‖ := by
      simpa using (norm_sum_le (Finset.univ : Finset (Fin 30))
        (fun family => record2680CorrectionCoefficient family *
          weightedUnitJet2539 order (-1 / 2) capturedModulations2584 family
            (record2680Center3212 index)))
    _ ≤ ∑ family : Fin 30,
        if cellNearAbs2538 (record2680Grid3212 index)
            (record2680Grid3212 (index + 1)) < storedWidth family ^ 2 then
          weightedFamilyCellUpper2538 order (record2680CorrectionCoefficient family)
            (-1 / 2) (capturedModulations2584 family) (storedWidth family ^ 2)
            (cellNearAbs2538 (record2680Grid3212 index)
              (record2680Grid3212 (index + 1)) / (storedWidth family ^ 2))
            (min (max |record2680Grid3212 index|
              |record2680Grid3212 (index + 1)|) (storedWidth family ^ 2) /
              (storedWidth family ^ 2))
            (record2680Grid3212 index) (record2680Grid3212 (index + 1))
        else 0 := by
      apply Finset.sum_le_sum
      intro family _
      by_cases hcross : cellNearAbs2538 (record2680Grid3212 index)
          (record2680Grid3212 (index + 1)) < storedWidth family ^ 2
      · have hradius : 0 < storedWidth family ^ 2 :=
          pow_pos (storedWidth_pos family) 2
        have hleft : record2680Grid3212 index <
            record2680Grid3212 (index + 1) :=
          record2680_grid_order3212 hindex
        have hcenter : record2680Center3212 index =
            (record2680Grid3212 index + record2680Grid3212 (index + 1)) / 2 :=
          record2680_center_midpoint3212 index
        have hposition : record2680Center3212 index ∈
            Set.Icc (record2680Grid3212 index)
              (record2680Grid3212 (index + 1)) := by
          rw [hcenter, Set.mem_Icc]
          constructor <;> linarith
        have heq : iteratedDeriv order
              (weightedFunction2348 (-1 / 2)
                (externalFamilyValue2344 (record2680CorrectionCoefficient family)
                  (capturedModulations2584 family) (storedWidth family ^ 2)))
              (record2680Center3212 index) =
            record2680CorrectionCoefficient family *
              weightedUnitJet2539 order (-1 / 2) capturedModulations2584 family
                (record2680Center3212 index) := by
          simpa [weightedUnitJet2539] using
            (weightedExternalFamily_coefficient_linear2539 order (-1 / 2)
              (record2680CorrectionCoefficient family)
              (capturedModulations2584 family)
              (position := record2680Center3212 index) hradius)
        by_cases hcenter_inside : |record2680Center3212 index| < storedWidth family ^ 2
        · have hnear_nonneg : 0 ≤ cellNearAbs2538 (record2680Grid3212 index)
              (record2680Grid3212 (index + 1)) / (storedWidth family ^ 2) := by
            exact div_nonneg (cellNearAbs2538_nonneg _ _) hradius.le
          have hnear_one : cellNearAbs2538 (record2680Grid3212 index)
              (record2680Grid3212 (index + 1)) / (storedWidth family ^ 2) < 1 := by
            exact (div_lt_one hradius).mpr hcross
          have hlower : cellNearAbs2538 (record2680Grid3212 index)
              (record2680Grid3212 (index + 1)) / (storedWidth family ^ 2) ≤
              |record2680Center3212 index / (storedWidth family ^ 2)| := by
            rw [abs_div, abs_of_pos hradius]
            exact div_le_div_of_nonneg_right
              (cellNearAbs2538_le hposition) hradius.le
          have hupper :
              |record2680Center3212 index / (storedWidth family ^ 2)| ≤
                min (max |record2680Grid3212 index|
                  |record2680Grid3212 (index + 1)|) (storedWidth family ^ 2) /
                  (storedWidth family ^ 2) := by
            rw [abs_div, abs_of_pos hradius]
            apply div_le_div_of_nonneg_right _ hradius.le
            apply le_min
            · exact cellAbs_le_max2538 hposition
            · exact le_of_lt hcenter_inside
          have hbound := weightedExternalFamily_iteratedDeriv_le_cell2538 order horder
            (-1 / 2) (record2680CorrectionCoefficient family)
            (capturedModulations2584 family) hradius hnear_nonneg hnear_one
            hlower hupper hposition
          rw [if_pos hcross, ← heq]
          exact hbound
        · have hz := weightedExternalFamily_iteratedDeriv_zero_outside2538 order (-1 / 2)
            (record2680CorrectionCoefficient family) (capturedModulations2584 family)
            hradius (not_lt.mp hcenter_inside)
          rw [← heq, hz, norm_zero]
          rw [if_pos hcross]
          exact weightedFamilyCellUpper2538_nonneg3224 order
            (record2680CorrectionCoefficient family) (-1 / 2)
            (capturedModulations2584 family) (storedWidth family ^ 2)
            (cellNearAbs2538 (record2680Grid3212 index)
              (record2680Grid3212 (index + 1)) / (storedWidth family ^ 2))
            (min (max |record2680Grid3212 index|
              |record2680Grid3212 (index + 1)|) (storedWidth family ^ 2) /
              (storedWidth family ^ 2))
            (record2680Grid3212 index) (record2680Grid3212 (index + 1)) hradius
            (by exact div_nonneg (cellNearAbs2538_nonneg _ _) hradius.le)
            (by exact (div_lt_one hradius).mpr hcross)
            (by positivity)
      · have hnear_le : cellNearAbs2538 (record2680Grid3212 index)
            (record2680Grid3212 (index + 1)) ≤
            |record2680Center3212 index| := by
          apply cellNearAbs2538_le
          rw [record2680_center_midpoint3212 index, Set.mem_Icc]
          constructor <;> linarith [record2680_grid_order3212 hindex]
        have houtside : storedWidth family ^ 2 ≤
            |record2680Center3212 index| := by
          exact (not_lt.mp hcross).trans hnear_le
        have hz := weightedExternalFamily_iteratedDeriv_zero_outside2538 order (-1 / 2)
          (record2680CorrectionCoefficient family) (capturedModulations2584 family)
          (pow_pos (storedWidth_pos family) 2) houtside
        have heq : iteratedDeriv order
              (weightedFunction2348 (-1 / 2)
                (externalFamilyValue2344 (record2680CorrectionCoefficient family)
                  (capturedModulations2584 family) (storedWidth family ^ 2)))
              (record2680Center3212 index) =
            record2680CorrectionCoefficient family *
              weightedUnitJet2539 order (-1 / 2) capturedModulations2584 family
                (record2680Center3212 index) := by
          simpa [weightedUnitJet2539] using
            (weightedExternalFamily_coefficient_linear2539 order (-1 / 2)
              (record2680CorrectionCoefficient family)
              (capturedModulations2584 family)
              (position := record2680Center3212 index)
              (pow_pos (storedWidth_pos family) 2))
        rw [if_neg hcross, ← heq, hz, norm_zero]

theorem record2680_cell_derivative_real_bound3224
    (order : ℕ) (horder : order ≤ 6) {index : ℕ} (hindex : index < 40960) :
    ‖iteratedDeriv order
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 index)‖ ≤
      record2680CellDerivativeUpper3224 order index := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584) order (record2680Center3212 index)
    (weightedPhysical2539_contDiff (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)]
  have hre : ‖(iteratedDeriv order
      (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 index)).re‖ ≤
      ‖iteratedDeriv order
        (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) (record2680Center3212 index)‖ := by
    simpa only [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm
        (iteratedDeriv order
          (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
            capturedModulations2584) (record2680Center3212 index)))
  exact hre.trans (record2680_cell_derivative_complex_bound3224 order horder hindex)

noncomputable def record2680CellSecondBound3224 (index : ℕ) : ℝ :=
  record2680CellDerivativeUpper3224 2 index

noncomputable def record2680CellFourthBound3224 (index : ℕ) : ℝ :=
  record2680CellDerivativeUpper3224 4 index

theorem record2680_cell_second_bound3224 {index : ℕ} (hindex : index < 40960) :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 index) ≤
      record2680CellSecondBound3224 index := by
  have hnorm := record2680_cell_derivative_real_bound3224 2 (by norm_num) hindex
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hnorm)

theorem record2680_cell_fourth_bound3224 {index : ℕ} (hindex : index < 40960) :
    iteratedDeriv 4
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 index) ≤
      record2680CellFourthBound3224 index := by
  have hnorm := record2680_cell_derivative_real_bound3224 4 (by norm_num) hindex
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hnorm)

end ConnesWeilRH.Dev
