import ConnesWeilRH.Dev.C1RouteAConcreteOwnerInteriorValue3228

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2680_weighted_value_upper_of_family4_phase3229
    {index : ℕ}
    (honly :
      externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
          (record2680Center3212 index) =
        externalFamilyValue2344 (record2680CorrectionCoefficient 4)
          (capturedModulations2584 4) (storedWidth 4 ^ 2)
          (record2680Center3212 index))
    (hphase :
      (record2680CorrectionCoefficient 4 *
        Complex.exp (((capturedModulations2584 4 * record2680Center3212 index : ℝ) : ℂ) *
          Complex.I)).re < 0)
    (hinside : |record2680Center3212 index| < storedWidth 4 ^ 2) :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 index) ≤ 0 := by
  unfold weightedExternal3201
  rw [honly, externalFamilyValue2344_re_eq_bump_cos_sin3217]
  have hbump : 0 < widthBump (storedWidth 4 ^ 2) (record2680Center3212 index) := by
    rw [widthBump, if_pos hinside]
    exact Real.exp_pos _
  calc
    Real.exp ((-1 / 2) * record2680Center3212 index) *
          ((record2680CorrectionCoefficient 4).re *
            widthBump (storedWidth 4 ^ 2) (record2680Center3212 index) *
            Real.cos (capturedModulations2584 4 * record2680Center3212 index) -
          (record2680CorrectionCoefficient 4).im *
            widthBump (storedWidth 4 ^ 2) (record2680Center3212 index) *
            Real.sin (capturedModulations2584 4 * record2680Center3212 index)) =
        Real.exp ((-1 / 2) * record2680Center3212 index) *
          (widthBump (storedWidth 4 ^ 2) (record2680Center3212 index) *
            (record2680CorrectionCoefficient 4 *
              Complex.exp (((capturedModulations2584 4 * record2680Center3212 index : ℝ) : ℂ) *
                Complex.I)).re) := by
      simp only [Complex.mul_re, expMulIre2676, expMulIim2676]
      ring
    _ ≤ 0 := (mul_neg_of_pos_of_neg (Real.exp_pos _) <|
      mul_neg_of_pos_of_neg hbump hphase).le

noncomputable def record2680InteriorPhaseCoarseRect3229 : ComplexRect2427 :=
  { reLo := (4 : ℝ) / 5
    reHi := 1
    imLo := (1 : ℝ) / 5
    imHi := (1 : ℝ) / 2 }

theorem record2680_40957_only_family4_3229 :
    externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 40957) =
      externalFamilyValue2344 (record2680CorrectionCoefficient 4)
        (capturedModulations2584 4) (storedWidth 4 ^ 2)
        (record2680Center3212 40957) := by
  unfold externalPhysical2344
  apply Finset.sum_eq_single (4 : Fin 30)
  · intro index _ hindex
    have houtside : ¬ |record2680Center3212 40957| < storedWidth index ^ 2 := by
      fin_cases index <;>
        norm_num [record2680Center3212, record2680Grid3212,
          diagnosticRadius3201, storedWidth, Fin.ext_iff] at *
    simp only [externalFamilyValue2344, if_neg houtside]
  · simp

theorem record2680_40957_phase_coarse_subset3229 :
    record2680InteriorPhaseCoarseRect3229.reLo ≤
        (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40957)) 9).reLo ∧
      (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40957)) 9).reHi ≤
        record2680InteriorPhaseCoarseRect3229.reHi ∧
      record2680InteriorPhaseCoarseRect3229.imLo ≤
        (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40957)) 9).imLo ∧
      (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40957)) 9).imHi ≤
        record2680InteriorPhaseCoarseRect3229.imHi := by
  norm_num [record2680InteriorPhaseCoarseRect3229,
    complexRectPowSq3218, phaseRect3218, phaseTaylorError3218,
    reExpIPartial2676, imExpIPartial2676, Matrix.cons_val_four,
    Matrix.cons_val_zero, capturedModulations2584, record2680Center3212,
    record2680Grid3212, diagnosticRadius3201, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
    storedWidth, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2680_40957_phase_scaled512_3229 :
    |(capturedModulations2584 4 * record2680Center3212 40957) / 512| ≤ 1 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201]

theorem record2680_40957_phase_mem3229 :
    record2680InteriorPhaseCoarseRect3229.Mem
      (Complex.exp (((capturedModulations2584 4 * record2680Center3212 40957 : ℝ) : ℂ) *
        Complex.I)) := by
  have hsmall := phaseRect_mem3218 record2680_40957_phase_scaled512_3229
  have hpow := complexRectPowSq_mem3218 hsmall 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hpow
  rw [complex_phase_eq_pow512_3218]
  apply rectSubset2676
    record2680_40957_phase_coarse_subset3229.1
    record2680_40957_phase_coarse_subset3229.2.1
    record2680_40957_phase_coarse_subset3229.2.2.1
    record2680_40957_phase_coarse_subset3229.2.2.2
    hpow

theorem record2680_40957_coeff_phase_neg3229 :
    (record2680CorrectionCoefficient 4 *
      Complex.exp (((capturedModulations2584 4 * record2680Center3212 40957 : ℝ) : ℂ) *
        Complex.I)).re < 0 := by
  have hmem := ComplexRect2427.mem_mul
    record2680_correction4_mem_coarse_box3218
    record2680_40957_phase_mem3229
  have hupper :
      (record2680Correction4CoarseRect3218.mul
        record2680InteriorPhaseCoarseRect3229).reHi < 0 := by
    norm_num [record2680Correction4CoarseRect3218,
      record2680InteriorPhaseCoarseRect3229, ComplexRect2427.mul,
      RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
  exact lt_of_le_of_lt hmem.2.1 hupper

theorem record2680_40957_weighted_value_upper3229 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 40957) ≤ 0 := by
  apply record2680_weighted_value_upper_of_family4_phase3229
    record2680_40957_only_family4_3229
    record2680_40957_coeff_phase_neg3229
  rw [record2680Center3212, record2680Grid3212, record2680Grid3212,
    diagnosticRadius3201]
  norm_num [storedWidth, Matrix.cons_val_four, abs_of_nonneg]

theorem record2680_40956_only_family4_3229 :
    externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 40956) =
      externalFamilyValue2344 (record2680CorrectionCoefficient 4)
        (capturedModulations2584 4) (storedWidth 4 ^ 2)
        (record2680Center3212 40956) := by
  unfold externalPhysical2344
  apply Finset.sum_eq_single (4 : Fin 30)
  · intro index _ hindex
    have houtside : ¬ |record2680Center3212 40956| < storedWidth index ^ 2 := by
      fin_cases index <;>
        norm_num [record2680Center3212, record2680Grid3212,
          diagnosticRadius3201, storedWidth, Fin.ext_iff] at *
    simp only [externalFamilyValue2344, if_neg houtside]
  · simp

theorem record2680_40956_phase_coarse_mem3229 :
    record2680InteriorPhaseCoarseRect3229.Mem
      (Complex.exp (((capturedModulations2584 4 * record2680Center3212 40956 : ℝ) : ℂ) *
        Complex.I)) := by
  have hsubset :
      record2680InteriorPhaseCoarseRect3229.reLo ≤
          (complexRectPowSq3218
            (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40956)) 9).reLo ∧
        (complexRectPowSq3218
            (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40956)) 9).reHi ≤
          record2680InteriorPhaseCoarseRect3229.reHi ∧
        record2680InteriorPhaseCoarseRect3229.imLo ≤
          (complexRectPowSq3218
            (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40956)) 9).imLo ∧
        (complexRectPowSq3218
            (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 40956)) 9).imHi ≤
          record2680InteriorPhaseCoarseRect3229.imHi := by
    norm_num [record2680InteriorPhaseCoarseRect3229,
      complexRectPowSq3218, phaseRect3218, phaseTaylorError3218,
      reExpIPartial2676, imExpIPartial2676, Matrix.cons_val_four,
      Matrix.cons_val_zero, capturedModulations2584, record2680Center3212,
      record2680Grid3212, diagnosticRadius3201, ComplexRect2427.mul,
      RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
      storedWidth, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hscaled :
      |(capturedModulations2584 4 * record2680Center3212 40956) / 512| ≤ 1 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero,
      capturedModulations2584, record2680Center3212, record2680Grid3212,
      diagnosticRadius3201]
  have hsmall := phaseRect_mem3218 hscaled
  have hpow := complexRectPowSq_mem3218 hsmall 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hpow
  rw [complex_phase_eq_pow512_3218]
  apply rectSubset2676 hsubset.1 hsubset.2.1 hsubset.2.2.1 hsubset.2.2.2
  exact hpow

theorem record2680_40956_coeff_phase_neg3229 :
    (record2680CorrectionCoefficient 4 *
      Complex.exp (((capturedModulations2584 4 * record2680Center3212 40956 : ℝ) : ℂ) *
        Complex.I)).re < 0 := by
  have hmem := ComplexRect2427.mem_mul
    record2680_correction4_mem_coarse_box3218
    record2680_40956_phase_coarse_mem3229
  have hupper :
      (record2680Correction4CoarseRect3218.mul
        record2680InteriorPhaseCoarseRect3229).reHi < 0 := by
    norm_num [record2680Correction4CoarseRect3218,
      record2680InteriorPhaseCoarseRect3229, ComplexRect2427.mul,
      RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
  exact lt_of_le_of_lt hmem.2.1 hupper

theorem record2680_40956_weighted_value_upper3229 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 40956) ≤ 0 := by
  apply record2680_weighted_value_upper_of_family4_phase3229
    record2680_40956_only_family4_3229
    record2680_40956_coeff_phase_neg3229
  rw [record2680Center3212, record2680Grid3212, record2680Grid3212,
    diagnosticRadius3201]
  norm_num [storedWidth, Matrix.cons_val_four, abs_of_nonneg]

end ConnesWeilRH.Dev
