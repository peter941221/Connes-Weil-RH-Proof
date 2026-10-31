import ConnesWeilRH.Dev.C1RouteAConcreteOwnerMidpointSupport3217
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteARepairedOwnerCorrectionM02680
namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def complexRectPow3218 (rect : ComplexRect2427) : ℕ → ComplexRect2427
  | 0 => ComplexRect2427.point 1
  | n + 1 => (complexRectPow3218 rect n).mul rect

noncomputable def complexRectPowSq3218 (rect : ComplexRect2427) : ℕ → ComplexRect2427
  | 0 => rect
  | n + 1 => (complexRectPowSq3218 rect n).mul
      (complexRectPowSq3218 rect n)

noncomputable def phaseTaylorError3218 (angle : ℝ) : ℝ :=
  |angle / 512| ^ 26 * ((26 : Nat).succ /
    ((26 : Nat).factorial * 26))

noncomputable def phaseRect3218 (angle : ℝ) : ComplexRect2427 :=
  { reLo := (expIPartial2676 (angle / 512) 26).re - phaseTaylorError3218 angle
    reHi := (expIPartial2676 (angle / 512) 26).re + phaseTaylorError3218 angle
    imLo := (expIPartial2676 (angle / 512) 26).im - phaseTaylorError3218 angle
    imHi := (expIPartial2676 (angle / 512) 26).im + phaseTaylorError3218 angle }

noncomputable def record2680FirstCenterPhaseCoarseRect3218 : ComplexRect2427 :=
  { reLo := (9 : ℝ) / 10
    reHi := 1
    imLo := -(2 : ℝ) / 5
    imHi := -(3 : ℝ) / 10 }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- The exact rational interval expansion needs more than the default heartbeat budget.
theorem record2680_first_center_phase_coarse_subset3218 :
    record2680FirstCenterPhaseCoarseRect3218.reLo ≤
        (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 0)) 9).reLo ∧
      (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 0)) 9).reHi ≤
        record2680FirstCenterPhaseCoarseRect3218.reHi ∧
      record2680FirstCenterPhaseCoarseRect3218.imLo ≤
        (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 0)) 9).imLo ∧
      (complexRectPowSq3218
          (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 0)) 9).imHi ≤
        record2680FirstCenterPhaseCoarseRect3218.imHi := by
  norm_num [record2680FirstCenterPhaseCoarseRect3218, complexRectPowSq3218,
    phaseRect3218, phaseTaylorError3218, reExpIPartial2676,
    imExpIPartial2676, Matrix.cons_val_four, Matrix.cons_val_zero,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201, ComplexRect2427.mul, RealInterval2429.mul,
    RealInterval2429.add, RealInterval2429.sub, storedWidth,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

theorem complexRectPowSq_mem3218 {rect : ComplexRect2427} {z : ℂ}
    (hz : rect.Mem z) (n : ℕ) :
    (complexRectPowSq3218 rect n).Mem (z ^ (2 ^ n)) := by
  induction n with
  | zero =>
      simpa [complexRectPowSq3218] using hz
  | succ n ih =>
      have hmul := ComplexRect2427.mem_mul ih ih
      have hpow : z ^ (2 ^ (n + 1)) = (z ^ (2 ^ n)) ^ 2 := by
        rw [show 2 ^ (n + 1) = (2 ^ n) * 2 by ring, pow_mul]
      simpa [complexRectPowSq3218, pow_two, hpow] using hmul

theorem phaseRect_mem3218 {angle : ℝ} (hangle : |angle / 512| ≤ 1) :
    (phaseRect3218 angle).Mem
      (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hcos := cosPin2676 (angle / 512) hangle
    (P := (expIPartial2676 (angle / 512) 26).re)
    (E := phaseTaylorError3218 angle) rfl rfl
  have hsin := sinPin2676 (angle / 512) hangle
    (P := (expIPartial2676 (angle / 512) 26).im)
    (E := phaseTaylorError3218 angle) rfl rfl
  have hre :
      (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)).re =
        Real.cos (angle / 512) := by
    exact expMulIre2676 (angle / 512)
  have him :
      (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)).im =
        Real.sin (angle / 512) := by
    exact expMulIim2676 (angle / 512)
  rw [ComplexRect2427.Mem, hre, him]
  exact ⟨hcos.1, hcos.2, hsin.1, hsin.2⟩

theorem complexRectPow_mem3218 {rect : ComplexRect2427} {z : ℂ}
    (hz : rect.Mem z) (n : ℕ) :
    (complexRectPow3218 rect n).Mem (z ^ n) := by
  induction n with
  | zero =>
      simpa [complexRectPow3218] using (ComplexRect2427.point_mem (1 : ℂ))
  | succ n ih =>
      rw [pow_succ]
      exact ComplexRect2427.mem_mul ih hz

theorem complex_phase_eq_pow512_3218 (angle : ℝ) :
    Complex.exp ((angle : ℂ) * Complex.I) =
      Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I) ^ 512 := by
  have harg :
      (512 : ℂ) * (((angle / 512 : ℝ) : ℂ) * Complex.I) =
        (angle : ℂ) * Complex.I := by
    push_cast
    field_simp
  calc
    Complex.exp ((angle : ℂ) * Complex.I) =
        Complex.exp (512 * (((angle / 512 : ℝ) : ℂ) * Complex.I)) := by
      rw [harg]
    _ = Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I) ^ 512 := by
      simpa using
        (Complex.exp_nat_mul (((angle / 512 : ℝ) : ℂ) * Complex.I) 512)

theorem record2680_first_center_phase_scaled512_3218 :
    |(capturedModulations2584 4 * record2680Center3212 0) / 512| ≤ 1 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201]

theorem record2680_first_center_phase_rect_mem3218 :
    (complexRectPowSq3218
      (phaseRect3218 (capturedModulations2584 4 * record2680Center3212 0)) 9).Mem
      (Complex.exp (((capturedModulations2584 4 * record2680Center3212 0 : ℝ) : ℂ) *
        Complex.I)) := by
  have hsmall :
      (phaseRect3218
        (capturedModulations2584 4 * record2680Center3212 0)).Mem
        (Complex.exp ((((capturedModulations2584 4 * record2680Center3212 0) /
          512 : ℝ) : ℂ) * Complex.I)) := by
    exact phaseRect_mem3218 record2680_first_center_phase_scaled512_3218
  have hpow := complexRectPowSq_mem3218 hsmall 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hpow
  rw [complex_phase_eq_pow512_3218]
  exact hpow

noncomputable def record2680Correction4CoarseRect3218 : ComplexRect2427 :=
  { reLo := -(200000000000000 : ℝ), reHi := -(100000000000000 : ℝ)
    imLo := -(100000000000000 : ℝ), imHi := 0 }

theorem record2680_correction4_mem_coarse_box3218 :
    record2680Correction4CoarseRect3218.Mem (record2680CorrectionCoefficient 4) := by
  change -(200000000000000 : ℝ) ≤ (record2680CorrectionCoefficient 4).re ∧
    (record2680CorrectionCoefficient 4).re ≤ -(100000000000000 : ℝ) ∧
    -(100000000000000 : ℝ) ≤ (record2680CorrectionCoefficient 4).im ∧
    (record2680CorrectionCoefficient 4).im ≤ 0
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, record2680CorrectionCoefficient,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

theorem record2680_correction4_phase_product_upper3218 :
    ((record2680Correction4CoarseRect3218.mul
        record2680FirstCenterPhaseCoarseRect3218).reHi < 0) := by
  norm_num [record2680Correction4CoarseRect3218,
    record2680FirstCenterPhaseCoarseRect3218, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]


theorem record2680_first_center_bump_pos3218 :
    0 < widthBump (storedWidth 4 ^ 2) (record2680Center3212 0) := by
  have hradius : 0 < storedWidth 4 ^ 2 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, storedWidth, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
  have hinside : |record2680Center3212 0| < storedWidth 4 ^ 2 :=
    record2680_first_center_inside_ownerRadius3215
  rw [widthBump, if_pos hinside]
  exact Real.exp_pos _

theorem record2680_first_center_phase_coarse_mem3218 :
    record2680FirstCenterPhaseCoarseRect3218.Mem
      (Complex.exp (((capturedModulations2584 4 * record2680Center3212 0 : ℝ) : ℂ) *
        Complex.I)) := by
  apply rectSubset2676
    record2680_first_center_phase_coarse_subset3218.1
    record2680_first_center_phase_coarse_subset3218.2.1
    record2680_first_center_phase_coarse_subset3218.2.2.1
    record2680_first_center_phase_coarse_subset3218.2.2.2
    record2680_first_center_phase_rect_mem3218

theorem record2680_first_center_coeff_phase_mem3218 :
    (record2680Correction4CoarseRect3218.mul
        record2680FirstCenterPhaseCoarseRect3218).Mem
      (record2680CorrectionCoefficient 4 *
        Complex.exp (((capturedModulations2584 4 * record2680Center3212 0 : ℝ) : ℂ) *
          Complex.I)) := by
  exact ComplexRect2427.mem_mul
    record2680_correction4_mem_coarse_box3218
    record2680_first_center_phase_coarse_mem3218

theorem record2680_first_center_coeff_phase_re_neg3218 :
    ((record2680CorrectionCoefficient 4 *
        Complex.exp (((capturedModulations2584 4 * record2680Center3212 0 : ℝ) : ℂ) *
          Complex.I)).re < 0) := by
  have hmem := record2680_first_center_coeff_phase_mem3218
  have hupper := record2680_correction4_phase_product_upper3218
  exact lt_of_le_of_lt hmem.2.1 hupper

theorem record2680_first_center_family4_re_bump_mul3218 :
    (externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 0)).re =
      widthBump (storedWidth 4 ^ 2) (record2680Center3212 0) *
        (record2680CorrectionCoefficient 4 *
          Complex.exp (((capturedModulations2584 4 * record2680Center3212 0 : ℝ) : ℂ) *
            Complex.I)).re := by
  rw [record2680_first_center_family4_re_formula3217]
  simp only [Complex.mul_re, expMulIre2676, expMulIim2676]
  ring

theorem record2680_first_center_family4_re_neg3218 :
    (externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 0)).re < 0 := by
  rw [record2680_first_center_family4_re_bump_mul3218]
  exact mul_neg_of_pos_of_neg record2680_first_center_bump_pos3218
    record2680_first_center_coeff_phase_re_neg3218

theorem record2680_first_center_physical_re_neg3218 :
    (externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 0)).re < 0 := by
  have hfamily := record2680_first_center_family4_re_neg3218
  rw [record2680_first_center_only_family4_3217] at hfamily
  calc
    (externalPhysical2344 record2680CorrectionCoefficient capturedModulations2584
        (record2680Center3212 0)).re =        (externalFamilyValue2344 (record2680CorrectionCoefficient 4)
          (capturedModulations2584 4) (storedWidth 4 ^ 2)
          (record2680Center3212 0)).re := by
      rw [record2680_first_center_only_family4_3217]
    _ < 0 := hfamily

theorem record2680_first_center_weighted_re_neg3218 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 0) < 0 := by
  unfold weightedExternal3201
  exact mul_neg_of_pos_of_neg (Real.exp_pos _)
    record2680_first_center_physical_re_neg3218

theorem record2680_first_center_weighted_value_upper3218 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
         capturedModulations2584 (record2680Center3212 0) ≤ 0 := by
  exact (record2680_first_center_weighted_re_neg3218).le

end ConnesWeilRH.Dev