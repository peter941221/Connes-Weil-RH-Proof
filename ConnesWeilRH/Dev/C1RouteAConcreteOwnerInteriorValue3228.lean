import ConnesWeilRH.Dev.C1RouteAConcreteOwnerOuterValue3226

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680InteriorPhaseCoarseRect3228 : ComplexRect2427 :=
  { reLo := (9 : ℝ) / 10
    reHi := 1
    imLo := (3 : ℝ) / 10
    imHi := (2 : ℝ) / 5 }

theorem record2680_interior_center_only_family4_3228 :
    externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 40958) =
      externalFamilyValue2344 (record2680CorrectionCoefficient 4)
        (capturedModulations2584 4) (storedWidth 4 ^ 2)
        (record2680Center3212 40958) := by
  unfold externalPhysical2344
  apply Finset.sum_eq_single (4 : Fin 30)
  · intro index _ hindex
    have houtside : ¬ |record2680Center3212 40958| < storedWidth index ^ 2 := by
      fin_cases index <;>
        norm_num [record2680Center3212, record2680Grid3212,
          diagnosticRadius3201, storedWidth, Fin.ext_iff] at *
    simp only [externalFamilyValue2344, if_neg houtside]
  · simp

theorem record2680_interior_phase_coarse_subset3228 :
    record2680InteriorPhaseCoarseRect3228.reLo ≤
        (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40958)) 9).reLo ∧
      (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40958)) 9).reHi ≤
        record2680InteriorPhaseCoarseRect3228.reHi ∧
      record2680InteriorPhaseCoarseRect3228.imLo ≤
        (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40958)) 9).imLo ∧
      (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40958)) 9).imHi ≤
        record2680InteriorPhaseCoarseRect3228.imHi := by
  norm_num [record2680InteriorPhaseCoarseRect3228, complexRectPowSq3218,
    phaseRect3218, phaseTaylorError3218, reExpIPartial2676,
    imExpIPartial2676, Matrix.cons_val_four, Matrix.cons_val_zero,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, storedWidth,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

theorem record2680_interior_phase_scaled512_3228 :
    |(capturedModulations2584 4 * record2680Center3212 40958) / 512| ≤ 1 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201]

theorem record2680_interior_phase_rect_mem3228 :
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40958)) 9).Mem
      (Complex.exp (((capturedModulations2584 4 * record2680Center3212 40958 : ℝ) : ℂ) *
        Complex.I)) := by
  have hsmall := phaseRect_mem3218
    record2680_interior_phase_scaled512_3228
  have hpow := complexRectPowSq_mem3218 hsmall 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hpow
  rw [complex_phase_eq_pow512_3218]
  exact hpow

theorem record2680_interior_phase_coarse_mem3228 :
    record2680InteriorPhaseCoarseRect3228.Mem
      (Complex.exp (((capturedModulations2584 4 * record2680Center3212 40958 : ℝ) : ℂ) *
        Complex.I)) := by
  apply rectSubset2676
    record2680_interior_phase_coarse_subset3228.1
    record2680_interior_phase_coarse_subset3228.2.1
    record2680_interior_phase_coarse_subset3228.2.2.1
    record2680_interior_phase_coarse_subset3228.2.2.2
    record2680_interior_phase_rect_mem3228

theorem record2680_interior_coeff_phase_mem3228 :
    (record2680Correction4CoarseRect3218.mul
        record2680InteriorPhaseCoarseRect3228).Mem
      (record2680CorrectionCoefficient 4 *
        Complex.exp (((capturedModulations2584 4 * record2680Center3212 40958 : ℝ) : ℂ) *
          Complex.I)) := by
  exact ComplexRect2427.mem_mul
    record2680_correction4_mem_coarse_box3218
    record2680_interior_phase_coarse_mem3228

theorem record2680_interior_coeff_phase_re_upper3228 :
    ((record2680Correction4CoarseRect3218.mul
        record2680InteriorPhaseCoarseRect3228).reHi < 0) := by
  norm_num [record2680Correction4CoarseRect3218,
    record2680InteriorPhaseCoarseRect3228, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]

theorem record2680_interior_center_family4_re_neg3228 :
    (externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 40958)).re < 0 := by
  have hmem := record2680_interior_coeff_phase_mem3228
  have hupper := record2680_interior_coeff_phase_re_upper3228
  have hphase :
      (record2680CorrectionCoefficient 4 *
        Complex.exp (((capturedModulations2584 4 * record2680Center3212 40958 : ℝ) : ℂ) *
          Complex.I)).re < 0 :=
    lt_of_le_of_lt hmem.2.1 hupper
  rw [record2680_interior_center_only_family4_3228]
  rw [externalFamilyValue2344_re_eq_bump_cos_sin3217]
  have hbump : 0 < widthBump (storedWidth 4 ^ 2) (record2680Center3212 40958) := by
    rw [widthBump]
    have hinside : |record2680Center3212 40958| < storedWidth 4 ^ 2 := by
      rw [record2680Center3212, record2680Grid3212,
        record2680Grid3212, diagnosticRadius3201]
      norm_num [storedWidth, Matrix.cons_val_four, abs_of_nonneg]
    rw [if_pos hinside]
    exact Real.exp_pos _
  calc
    (record2680CorrectionCoefficient 4).re *
          widthBump (storedWidth 4 ^ 2) (record2680Center3212 40958) *
          Real.cos (capturedModulations2584 4 * record2680Center3212 40958) -
        (record2680CorrectionCoefficient 4).im *
          widthBump (storedWidth 4 ^ 2) (record2680Center3212 40958) *
          Real.sin (capturedModulations2584 4 * record2680Center3212 40958) =
      widthBump (storedWidth 4 ^ 2) (record2680Center3212 40958) *
        (record2680CorrectionCoefficient 4 *
          Complex.exp (((capturedModulations2584 4 * record2680Center3212 40958 : ℝ) : ℂ) *
            Complex.I)).re := by
      simp only [Complex.mul_re, expMulIre2676, expMulIim2676]
      ring
    _ < 0 := mul_neg_of_pos_of_neg hbump hphase

theorem record2680_interior_center_weighted_value_upper3228 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 40958) ≤ 0 := by
  unfold weightedExternal3201
  exact (mul_neg_of_pos_of_neg (Real.exp_pos _)
    record2680_interior_center_family4_re_neg3228).le

end ConnesWeilRH.Dev
