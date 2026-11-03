import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamilies11to14TightStaged3264

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell17168Family10CoeffPhaseRect3265 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 10)).mul
    (record2680Cell17168Family10TightStageBox3256 9)

noncomputable def record2680Cell17168Family11CoeffPhaseRect3265 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 11)).mul
    (record2680Cell17168Family11TightStageBox3264 9)

noncomputable def record2680Cell17168Family12CoeffPhaseRect3265 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 12)).mul
    (record2680Cell17168Family12TightStageBox3264 9)

noncomputable def record2680Cell17168Family13CoeffPhaseRect3265 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 13)).mul
    (record2680Cell17168Family13TightStageBox3264 9)

noncomputable def record2680Cell17168Family14CoeffPhaseRect3265 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 14)).mul
    (record2680Cell17168Family14TightStageBox3264 9)

noncomputable def record2680Cell17168CoeffPhaseBlock10to14Rect3265 : ComplexRect2427 :=
  (((record2680Cell17168Family10CoeffPhaseRect3265.add
      record2680Cell17168Family11CoeffPhaseRect3265).add
      record2680Cell17168Family12CoeffPhaseRect3265).add
      record2680Cell17168Family13CoeffPhaseRect3265).add
      record2680Cell17168Family14CoeffPhaseRect3265

noncomputable def record2680Cell17168CoeffPhaseBlock10to14Value3265 : ℂ :=
  let z10 := record2680CorrectionCoefficient 10 *
    Complex.exp (((capturedModulations2584 10 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)
  let z11 := record2680CorrectionCoefficient 11 *
    Complex.exp (((capturedModulations2584 11 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)
  let z12 := record2680CorrectionCoefficient 12 *
    Complex.exp (((capturedModulations2584 12 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)
  let z13 := record2680CorrectionCoefficient 13 *
    Complex.exp (((capturedModulations2584 13 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)
  let z14 := record2680CorrectionCoefficient 14 *
    Complex.exp (((capturedModulations2584 14 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)
  (((z10 + z11) + z12) + z13) + z14

theorem record2680_cell17168_family10_coeff_phase_mem3265 :
    record2680Cell17168Family10CoeffPhaseRect3265.Mem
      (record2680CorrectionCoefficient 10 *
        Complex.exp (((capturedModulations2584 10 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul (ComplexRect2427.point_mem _)
    record2680_cell17168_family10_tight_phase_box_mem3256

theorem record2680_cell17168_family11_coeff_phase_mem3265 :
    record2680Cell17168Family11CoeffPhaseRect3265.Mem
      (record2680CorrectionCoefficient 11 *
        Complex.exp (((capturedModulations2584 11 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul (ComplexRect2427.point_mem _)
    record2680_cell17168_family11_tight_phase_box_mem3264

theorem record2680_cell17168_family12_coeff_phase_mem3265 :
    record2680Cell17168Family12CoeffPhaseRect3265.Mem
      (record2680CorrectionCoefficient 12 *
        Complex.exp (((capturedModulations2584 12 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul (ComplexRect2427.point_mem _)
    record2680_cell17168_family12_tight_phase_box_mem3264

theorem record2680_cell17168_family13_coeff_phase_mem3265 :
    record2680Cell17168Family13CoeffPhaseRect3265.Mem
      (record2680CorrectionCoefficient 13 *
        Complex.exp (((capturedModulations2584 13 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul (ComplexRect2427.point_mem _)
    record2680_cell17168_family13_tight_phase_box_mem3264

theorem record2680_cell17168_family14_coeff_phase_mem3265 :
    record2680Cell17168Family14CoeffPhaseRect3265.Mem
      (record2680CorrectionCoefficient 14 *
        Complex.exp (((capturedModulations2584 14 * record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  exact ComplexRect2427.mem_mul (ComplexRect2427.point_mem _)
    record2680_cell17168_family14_tight_phase_box_mem3264

theorem record2680_cell17168_coeff_phase_block10to14_mem3265 :
    record2680Cell17168CoeffPhaseBlock10to14Rect3265.Mem
      record2680Cell17168CoeffPhaseBlock10to14Value3265 := by
  simp only [record2680Cell17168CoeffPhaseBlock10to14Value3265]
  apply ComplexRect2427.mem_add
  · apply ComplexRect2427.mem_add
    · apply ComplexRect2427.mem_add
      · apply ComplexRect2427.mem_add
        · exact record2680_cell17168_family10_coeff_phase_mem3265
        · exact record2680_cell17168_family11_coeff_phase_mem3265
      · exact record2680_cell17168_family12_coeff_phase_mem3265
    · exact record2680_cell17168_family13_coeff_phase_mem3265
  · exact record2680_cell17168_family14_coeff_phase_mem3265

theorem record2680_cell17168_family10_coeff_phase_re_lower3265 :
    record2680Cell17168Family10CoeffPhaseRect3265.reLo ≥
      (-1000000000000000 : ℝ) := by
  norm_num [record2680Cell17168Family10CoeffPhaseRect3265,
    record2680Cell17168Family10TightStageBox3256, ComplexRect2427.point,
    ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
    RealInterval2429.sub, min_def, max_def, record2680CorrectionCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_10,
    Fin.ext_iff, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2680_cell17168_family11_coeff_phase_re_lower3265 :
    record2680Cell17168Family11CoeffPhaseRect3265.reLo ≥
      (-2000000000000000 : ℝ) := by
  norm_num [record2680Cell17168Family11CoeffPhaseRect3265,
    record2680Cell17168Family11TightStageBox3264, ComplexRect2427.point,
    ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
    RealInterval2429.sub, min_def, max_def, record2680CorrectionCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_11,
    Fin.ext_iff, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2680_cell17168_family12_coeff_phase_re_lower3265 :
    record2680Cell17168Family12CoeffPhaseRect3265.reLo ≥
      (-3000000000000000 : ℝ) := by
  norm_num [record2680Cell17168Family12CoeffPhaseRect3265,
    record2680Cell17168Family12TightStageBox3264, ComplexRect2427.point,
    ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
    RealInterval2429.sub, min_def, max_def, record2680CorrectionCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_12,
    Fin.ext_iff, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2680_cell17168_family13_coeff_phase_re_lower3265 :
    record2680Cell17168Family13CoeffPhaseRect3265.reLo ≥
      (0 : ℝ) := by
  norm_num [record2680Cell17168Family13CoeffPhaseRect3265,
    record2680Cell17168Family13TightStageBox3264, ComplexRect2427.point,
    ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
    RealInterval2429.sub, min_def, max_def, record2680CorrectionCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_13,
    Fin.ext_iff, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2680_cell17168_family14_coeff_phase_re_lower3265 :
    record2680Cell17168Family14CoeffPhaseRect3265.reLo ≥
      (200000000000000000 : ℝ) := by
  norm_num [record2680Cell17168Family14CoeffPhaseRect3265,
    record2680Cell17168Family14TightStageBox3264, ComplexRect2427.point,
    ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
    RealInterval2429.sub, min_def, max_def, record2680CorrectionCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_14,
    Fin.ext_iff, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

theorem record2680_cell17168_coeff_phase_block10to14_re_lower3265 :
    (200000000000000000 : ℝ) ≤
      record2680Cell17168CoeffPhaseBlock10to14Rect3265.reLo := by
  norm_num [record2680Cell17168CoeffPhaseBlock10to14Rect3265,
    record2680Cell17168Family10CoeffPhaseRect3265,
    record2680Cell17168Family11CoeffPhaseRect3265,
    record2680Cell17168Family12CoeffPhaseRect3265,
    record2680Cell17168Family13CoeffPhaseRect3265,
    record2680Cell17168Family14CoeffPhaseRect3265,
    ComplexRect2427.point, ComplexRect2427.add, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
    min_def, max_def, record2680CorrectionCoefficient,
    record2680Cell17168Family10TightStageBox3256,
    record2680Cell17168Family11TightStageBox3264,
    record2680Cell17168Family12TightStageBox3264,
    record2680Cell17168Family13TightStageBox3264,
    record2680Cell17168Family14TightStageBox3264,
    Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_10,
    Matrix.cons_val_11, Matrix.cons_val_12, Matrix.cons_val_13,
    Matrix.cons_val_14, Fin.ext_iff, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

theorem record2680_cell17168_coeff_phase_block10to14_re_pos3265 :
    0 < record2680Cell17168CoeffPhaseBlock10to14Value3265.re := by
  have hmem := record2680_cell17168_coeff_phase_block10to14_mem3265
  have hlower : (200000000000000000 : ℝ) ≤
      record2680Cell17168CoeffPhaseBlock10to14Rect3265.reLo :=
    record2680_cell17168_coeff_phase_block10to14_re_lower3265
  exact lt_of_lt_of_le (by norm_num) (hlower.trans hmem.1)

end ConnesWeilRH.Dev
