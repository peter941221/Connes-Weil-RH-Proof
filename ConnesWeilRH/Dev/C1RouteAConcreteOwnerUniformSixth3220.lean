import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellUpper3208

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/-
  The real-valued producer function is the real part of a complex-valued
  physical sum.  This lemma makes that projection explicit at the level of
  iterated derivatives, so the existing complex family envelope can be used
  without changing the owner or discarding signed family data.
-/
theorem iteratedDeriv_re_eq_re_iteratedDeriv3220
    (f : ℝ → ℂ) (order : ℕ) (coordinate : ℝ)
    (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv order (fun x => (f x).re) coordinate =
      (iteratedDeriv order f coordinate).re := by
  induction order generalizing coordinate with
  | zero => rfl
  | succ order ih =>
      rw [iteratedDeriv_succ]
      have hi : iteratedDeriv order (fun x => (f x).re) =
          fun x => (iteratedDeriv order f x).re := by
        funext x
        exact ih x
      rw [hi]
      have hf' : ContDiff ℝ (order + 1) f := hf.of_le
        (by exact_mod_cast (le_top : (order + 1 : ℕ∞) ≤ ⊤))
      have hu : DifferentiableAt ℝ (iteratedDeriv order f) coordinate :=
        (hf'.differentiable_iteratedDeriv' order) coordinate
      have hc : DifferentiableAt ℝ (fun _ : ℝ => Complex.reCLM) coordinate :=
        differentiableAt_const _
      have h := deriv_clm_apply hc hu
      rw [← iteratedDeriv_succ] at h
      simpa using h

noncomputable def record2680UniformSixthUpper3220 : ℝ :=
  ∑ index : Fin 30,
    weightedFamilyCellUpper2538 6 (record2680CorrectionCoefficient index)
      (-1 / 2) (capturedModulations2584 index) (storedWidth index ^ 2)
      0 1 (-(storedWidth index ^ 2)) (storedWidth index ^ 2)

theorem record2680_uniform_sixth_complex_bound3220 (coordinate : ℝ) :
    ‖iteratedDeriv 6
      (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate‖ ≤
      record2680UniformSixthUpper3220 := by
  rw [weightedPhysical2539_iteratedDeriv]
  unfold record2680UniformSixthUpper3220
  calc
    ‖∑ index : Fin 30,
        record2680CorrectionCoefficient index *
          weightedUnitJet2539 6 (-1 / 2) capturedModulations2584 index coordinate‖ ≤
        ∑ index : Fin 30, ‖record2680CorrectionCoefficient index *
          weightedUnitJet2539 6 (-1 / 2) capturedModulations2584 index coordinate‖ := by
      simpa using (norm_sum_le (Finset.univ : Finset (Fin 30))
        (fun index => record2680CorrectionCoefficient index *
          weightedUnitJet2539 6 (-1 / 2) capturedModulations2584 index coordinate))
    _ ≤ ∑ index : Fin 30,
        weightedFamilyCellUpper2538 6 (record2680CorrectionCoefficient index)
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
          rw [Set.mem_Icc]
          rw [← abs_le]
          exact le_of_lt hinside
        have hbound := weightedExternalFamily_iteratedDeriv_le_cell2538 6
          (by norm_num) (-1 / 2) (record2680CorrectionCoefficient index)
          (capturedModulations2584 index) hradius
          (by norm_num) (by norm_num) hratio_nonneg hratio_le_one hposition
        have heq : iteratedDeriv 6
              (weightedFunction2348 (-1 / 2)
                (externalFamilyValue2344 (record2680CorrectionCoefficient index)
                  (capturedModulations2584 index) (storedWidth index ^ 2))) coordinate =
            record2680CorrectionCoefficient index *
              weightedUnitJet2539 6 (-1 / 2) capturedModulations2584 index coordinate := by
          simpa [weightedUnitJet2539] using
            (weightedExternalFamily_coefficient_linear2539 6 (-1 / 2)
              (record2680CorrectionCoefficient index)
              (capturedModulations2584 index) (position := coordinate) hradius)
        rw [← heq]
        exact hbound
      · have houtside : storedWidth index ^ 2 ≤ |coordinate| := not_lt.mp hinside
        have hz := weightedExternalFamily_iteratedDeriv_zero_outside2538 6 (-1 / 2)
          (record2680CorrectionCoefficient index) (capturedModulations2584 index)
          (pow_pos (storedWidth_pos index) 2) houtside
        have heq : iteratedDeriv 6
              (weightedFunction2348 (-1 / 2)
                (externalFamilyValue2344 (record2680CorrectionCoefficient index)
                  (capturedModulations2584 index) (storedWidth index ^ 2))) coordinate =
            record2680CorrectionCoefficient index *
              weightedUnitJet2539 6 (-1 / 2) capturedModulations2584 index coordinate := by
          simpa [weightedUnitJet2539] using
            (weightedExternalFamily_coefficient_linear2539 6 (-1 / 2)
              (record2680CorrectionCoefficient index)
              (capturedModulations2584 index) (position := coordinate)
              (pow_pos (storedWidth_pos index) 2))
        rw [← heq, hz, norm_zero]
        have hsum : 0 ≤ ∑ index' ∈ Finset.range (6 + 1),
            (Nat.choose 6 index' : ℝ) *
              ‖weightedLambda2537 (-1 / 2) (capturedModulations2584 index)‖ ^ index' *
              localCoupledBumpUpper2536 (6 - index') (storedWidth index ^ 2) 0 1 := by
          apply Finset.sum_nonneg
          intro index' _
          exact mul_nonneg (by positivity)
            (localCoupledBumpUpper2536_nonneg _
              (pow_pos (storedWidth_pos index) 2) (by norm_num) (by norm_num) (by norm_num))
        unfold weightedFamilyCellUpper2538
        exact mul_nonneg (norm_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) hsum)

theorem record2680_uniform_sixth_real_bound3220 (coordinate : ℝ) :
    ‖iteratedDeriv 6
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate‖ ≤
      record2680UniformSixthUpper3220 := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584) 6 coordinate
    (weightedPhysical2539_contDiff (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)]
  have hre : ‖(iteratedDeriv 6
      (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate).re‖ ≤
      ‖iteratedDeriv 6
        (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
          capturedModulations2584) coordinate‖ := by
    simpa only [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm
        (iteratedDeriv 6
          (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
            capturedModulations2584) coordinate))
  exact hre.trans (record2680_uniform_sixth_complex_bound3220 coordinate)

noncomputable def record2680UniformSixthBound3220 (_ : ℕ) : ℝ :=
  record2680UniformSixthUpper3220

theorem record2680_uniform_sixth_upper_nonneg3220 :
    0 ≤ record2680UniformSixthUpper3220 := by
  unfold record2680UniformSixthUpper3220
  apply Finset.sum_nonneg
  intro index _
  unfold weightedFamilyCellUpper2538
  have hsum : 0 ≤ ∑ index' ∈ Finset.range (6 + 1),
      (Nat.choose 6 index' : ℝ) *
        ‖weightedLambda2537 (-1 / 2) (capturedModulations2584 index)‖ ^ index' *
        localCoupledBumpUpper2536 (6 - index') (storedWidth index ^ 2) 0 1 := by
    apply Finset.sum_nonneg
    intro index' _
    exact mul_nonneg (by positivity)
      (localCoupledBumpUpper2536_nonneg _
        (pow_pos (storedWidth_pos index) 2) (by norm_num) (by norm_num) (by norm_num))
  exact mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) hsum)

theorem record2680_uniform_sixth_bound_nonneg3220 (index : ℕ) :
    0 ≤ record2680UniformSixthBound3220 index := by
  exact record2680_uniform_sixth_upper_nonneg3220

theorem record2680_uniform_sixth_array_bound3220
    {index : ℕ} (hindex : index < 40960) (coordinate : ℝ) :
    ‖iteratedDeriv 6
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) coordinate‖ ≤
      record2680UniformSixthBound3220 index := by
  exact record2680_uniform_sixth_real_bound3220 coordinate

end ConnesWeilRH.Dev
