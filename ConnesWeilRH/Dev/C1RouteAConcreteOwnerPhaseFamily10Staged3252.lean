import ConnesWeilRH.Dev.C1RouteAConcreteOwnerStagedPhasePower3251
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell17168Rect3245

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell17168Family10StageBox3252
    (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := -2, reHi := 2, imLo := -2, imHi := 2 }
  | 1 => { reLo := -8, reHi := 8, imLo := -8, imHi := 8 }
  | 2 => { reLo := -128, reHi := 128, imLo := -128, imHi := 128 }
  | 3 => { reLo := -32768, reHi := 32768, imLo := -32768, imHi := 32768 }
  | 4 => { reLo := -(2 ^ 31), reHi := 2 ^ 31, imLo := -(2 ^ 31), imHi := 2 ^ 31 }
  | 5 => { reLo := -(2 ^ 63), reHi := 2 ^ 63, imLo := -(2 ^ 63), imHi := 2 ^ 63 }
  | 6 => { reLo := -(2 ^ 127), reHi := 2 ^ 127, imLo := -(2 ^ 127), imHi := 2 ^ 127 }
  | 7 => { reLo := -(2 ^ 255), reHi := 2 ^ 255, imLo := -(2 ^ 255), imHi := 2 ^ 255 }
  | 8 => { reLo := -(2 ^ 511), reHi := 2 ^ 511, imLo := -(2 ^ 511), imHi := 2 ^ 511 }
  | _ => { reLo := -(2 ^ 1023), reHi := 2 ^ 1023, imLo := -(2 ^ 1023), imHi := 2 ^ 1023 }

noncomputable def record2680Cell17168Family10PhaseValue3252 : ℂ :=
  Complex.exp ((((capturedModulations2584 10 * record2680Center3212 17168) / 512 : ℝ) : ℂ) *
    Complex.I)

theorem phaseRect_subset_two3252 {angle : ℝ}
    (hangle : |angle / 512| ≤ 1) :
    (-2 : ℝ) ≤ (phaseRect3218 angle).reLo ∧
      (phaseRect3218 angle).reHi ≤ 2 ∧
      (-2 : ℝ) ≤ (phaseRect3218 angle).imLo ∧
      (phaseRect3218 angle).imHi ≤ 2 := by
  have hcos := cosPin2676 (angle / 512) hangle
    (P := (expIPartial2676 (angle / 512) 26).re)
    (E := phaseTaylorError3218 angle) rfl rfl
  have hsin := sinPin2676 (angle / 512) hangle
    (P := (expIPartial2676 (angle / 512) 26).im)
    (E := phaseTaylorError3218 angle) rfl rfl
  have herror : phaseTaylorError3218 angle ≤ (1 : ℝ) / 2 := by
    unfold phaseTaylorError3218
    have hpow : |angle / 512| ^ 26 ≤ (1 : ℝ) :=
      pow_le_one₀ (abs_nonneg _) hangle
    calc
      |angle / 512| ^ 26 *
          ((26 : Nat).succ / ((26 : Nat).factorial * 26)) ≤
          1 * ((26 : Nat).succ / ((26 : Nat).factorial * 26)) := by
            exact mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ (1 : ℝ) / 2 := by norm_num
  have hcosLo := Real.neg_one_le_cos (angle / 512)
  have hcosHi := Real.cos_le_one (angle / 512)
  have hsinLo := Real.neg_one_le_sin (angle / 512)
  have hsinHi := Real.sin_le_one (angle / 512)
  dsimp [phaseRect3218]
  constructor
  · nlinarith [hcos.2, hcosLo, herror]
  constructor
  · nlinarith [hcos.1, hcosHi, herror]
  constructor
  · nlinarith [hsin.2, hsinLo, herror]
  · nlinarith [hsin.1, hsinHi, herror]

theorem record2680_cell17168_family10_stage_base_mem3252 :
    (record2680Cell17168Family10StageBox3252 0).Mem
      record2680Cell17168Family10PhaseValue3252 := by
  have hscaled := record2680_cell17168_phase_scaled5123245 (family := (10 : Fin 30))
  have hphase := phaseRect_mem3218 hscaled
  have hbox := phaseRect_subset_two3252 hscaled
  refine rectSubset2676
    (inner := phaseRect3218
      (capturedModulations2584 10 * record2680Center3212 17168))
    hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2 hphase

set_option maxRecDepth 100000 in
theorem record2680_cell17168_family10_stage_step_mem3252
    {stage : ℕ} (hstage : stage < 9) {w : ℂ}
    (hw : (record2680Cell17168Family10StageBox3252 stage).Mem w) :
    (record2680Cell17168Family10StageBox3252 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676
    (inner := (record2680Cell17168Family10StageBox3252 stage).mul
      (record2680Cell17168Family10StageBox3252 stage)) ?_ ?_ ?_ ?_ hmul
  · interval_cases stage <;>
      norm_num [record2680Cell17168Family10StageBox3252,
        ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, pow_succ]
  · interval_cases stage <;>
      norm_num [record2680Cell17168Family10StageBox3252,
        ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, pow_succ]
  · interval_cases stage <;>
      norm_num [record2680Cell17168Family10StageBox3252,
        ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, pow_succ]
  · interval_cases stage <;>
      norm_num [record2680Cell17168Family10StageBox3252,
        ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub, pow_succ]

theorem record2680_cell17168_family10_staged_phase_box_mem3252 :
    (record2680Cell17168Family10StageBox3252 9).Mem
      (record2680Cell17168Family10PhaseValue3252 ^ 512) := by
  apply complexRectPowSq_staged_mem_of_bound3251
    record2680_cell17168_family10_stage_base_mem3252
  intro stage hstage w hw
  exact record2680_cell17168_family10_stage_step_mem3252 hstage hw

theorem record2680_cell17168_family10_staged_phase_box_mem_exp3252 :
    (record2680Cell17168Family10StageBox3252 9).Mem
      (Complex.exp (((capturedModulations2584 10 * record2680Center3212 17168 : ℝ) : ℂ) *
        Complex.I)) := by
  rw [complex_phase_eq_pow512_3218]
  exact record2680_cell17168_family10_staged_phase_box_mem3252

end ConnesWeilRH.Dev
