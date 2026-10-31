import ConnesWeilRH.Dev.C1RouteACorrelatedTaxiBall3235
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerMiddlePoint3231
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680MiddlePointPhaseBaseBall3236
    (angle : ℝ) : ComplexTaxiBall3235 :=
  { center := expIPartial2676 (angle / 512) 26
    radius := 2 * phaseTaylorError3218 angle }

theorem record2680_middle_point_phase_base_mem3236
    {angle : ℝ} (hangle : |angle / 512| ≤ 1) :
    (record2680MiddlePointPhaseBaseBall3236 angle).Mem
      (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hcos := cosPin2676 (angle / 512) hangle
    (P := (expIPartial2676 (angle / 512) 26).re)
    (E := phaseTaylorError3218 angle) rfl rfl
  have hsin := sinPin2676 (angle / 512) hangle
    (P := (expIPartial2676 (angle / 512) 26).im)
    (E := phaseTaylorError3218 angle) rfl rfl
  have herror : 0 ≤ phaseTaylorError3218 angle := by
    dsimp [phaseTaylorError3218]
    positivity
  have hre :
      |(Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)).re -
          (expIPartial2676 (angle / 512) 26).re| ≤
        phaseTaylorError3218 angle := by
    rw [expMulIre2676]
    rw [abs_le]
    constructor <;> linarith [hcos.1, hcos.2]
  have him :
      |(Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)).im -
          (expIPartial2676 (angle / 512) 26).im| ≤
        phaseTaylorError3218 angle := by
    rw [expMulIim2676]
    rw [abs_le]
    constructor <;> linarith [hsin.1, hsin.2]
  constructor
  · exact mul_nonneg (by norm_num) herror
  · calc
      taxiNorm3235
          (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I) -
            (record2680MiddlePointPhaseBaseBall3236 angle).center) =
          |(Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)).re -
              (expIPartial2676 (angle / 512) 26).re| +
            |(Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)).im -
              (expIPartial2676 (angle / 512) 26).im| := by
                simp [taxiNorm3235,
                  record2680MiddlePointPhaseBaseBall3236]
      _ ≤ phaseTaylorError3218 angle + phaseTaylorError3218 angle :=
        add_le_add hre him
      _ = 2 * phaseTaylorError3218 angle := by ring

noncomputable def record2680MiddlePointPhaseBall3236
    (angle : ℝ) : ℕ → ComplexTaxiBall3235
  | 0 => record2680MiddlePointPhaseBaseBall3236 angle
  | n + 1 =>
      (record2680MiddlePointPhaseBall3236 angle n).mul
        (record2680MiddlePointPhaseBall3236 angle n)

theorem record2680_middle_point_phase_ball_mem3236
    {angle : ℝ} (hangle : |angle / 512| ≤ 1) :
    ∀ n,
      (record2680MiddlePointPhaseBall3236 angle n).Mem
        ((Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)) ^ (2 ^ n)) := by
  intro n
  induction n with
  | zero =>
      simpa [record2680MiddlePointPhaseBall3236] using
        (record2680_middle_point_phase_base_mem3236 hangle)
  | succ n ih =>
      have hmul := ComplexTaxiBall3235.mem_mul ih ih
      have hpow :
          (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)) ^ (2 ^ n) *
              (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)) ^ (2 ^ n) =
            (Complex.exp (((angle / 512 : ℝ) : ℂ) * Complex.I)) ^ (2 ^ (n + 1)) := by
        rw [← pow_add]
        congr 1
        rw [pow_succ]
        ring
      rw [hpow] at hmul
      simpa [record2680MiddlePointPhaseBall3236] using hmul

noncomputable def record2680MiddlePointBumpBall3236
    (family : Fin 30) : ComplexTaxiBall3235 :=
  { center :=
      (((record2680MiddlePointBumpInterval3231 family).lo +
        (record2680MiddlePointBumpInterval3231 family).hi) / 2 : ℂ)
    radius :=
      ((record2680MiddlePointBumpInterval3231 family).hi -
        (record2680MiddlePointBumpInterval3231 family).lo) / 2 }

theorem record2680_middle_point_bump_ball_mem3236
    (family : Fin 30) :
    (record2680MiddlePointBumpBall3236 family).Mem
      (widthBump (storedWidth family ^ 2) (record2680Center3212 17168) : ℂ) := by
  have h := record2680_middle_point_bump_mem3231 (family := family)
  constructor
  · change 0 ≤
      ((record2680MiddlePointBumpInterval3231 family).hi -
        (record2680MiddlePointBumpInterval3231 family).lo) / 2
    linarith [h.1, h.2]
  · change
      taxiNorm3235
        ((widthBump (storedWidth family ^ 2)
          (record2680Center3212 17168) : ℂ) -
          (((record2680MiddlePointBumpInterval3231 family).lo +
            (record2680MiddlePointBumpInterval3231 family).hi) / 2 : ℂ)) ≤
        ((record2680MiddlePointBumpInterval3231 family).hi -
          (record2680MiddlePointBumpInterval3231 family).lo) / 2
    simp [taxiNorm3235, Complex.sub_re, Complex.sub_im,
      Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im]
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]

noncomputable def record2680MiddlePointFamilyBall3236
    (family : Fin 30) : ComplexTaxiBall3235 :=
  (ComplexTaxiBall3235.point (record2680CorrectionCoefficient family)).mul
    (record2680MiddlePointBumpBall3236 family)
    |>.mul (record2680MiddlePointPhaseBall3236
      (capturedModulations2584 family * record2680Center3212 17168) 9)

theorem record2680_middle_point_family_ball_mem3236
    {family : Fin 30} :
    (record2680MiddlePointFamilyBall3236 family).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family) (storedWidth family ^ 2)
        (record2680Center3212 17168)) := by
  have hscaled :
      |(capturedModulations2584 family * record2680Center3212 17168) / 512| ≤ 1 := by
    fin_cases family <;>
      norm_num [capturedModulations2584, record2680Center3212,
        record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff]
  have hphase := record2680_middle_point_phase_ball_mem3236 hscaled 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hphase
  have hphaseFull :
      (record2680MiddlePointPhaseBall3236
        (capturedModulations2584 family * record2680Center3212 17168) 9).Mem
        (Complex.exp (((capturedModulations2584 family *
          record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
    rw [complex_phase_eq_pow512_3218]
    exact hphase
  have hbump := record2680_middle_point_bump_ball_mem3236 family
  have hcoeff := ComplexTaxiBall3235.point_mem
    (record2680CorrectionCoefficient family)
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexTaxiBall3235.mem_mul
    (ComplexTaxiBall3235.mem_mul hcoeff hbump) hphaseFull

noncomputable def record2680MiddlePointAggregateBall3236 :
    ComplexTaxiBall3235 :=
  ComplexTaxiBall3235.sumFinset record2680MiddlePointFamilyBall3236 Finset.univ

theorem record2680_middle_point_aggregate_ball_mem3236 :
    record2680MiddlePointAggregateBall3236.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 (record2680Center3212 17168)) := by
  unfold record2680MiddlePointAggregateBall3236
  apply ComplexTaxiBall3235.mem_sumFinset
  intro family _
  exact record2680_middle_point_family_ball_mem3236

end ConnesWeilRH.Dev
