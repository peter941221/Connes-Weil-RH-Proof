import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell17168Rect3245
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerStagedPhasePower3251

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell17168Family10TightStageBox3256
    (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((998660509128 : ℝ) / 1000000000000), reHi := ((998660509130 : ℝ) / 1000000000000), imLo := ((51741545259 : ℝ) / 1000000000000), imHi := ((51741545261 : ℝ) / 1000000000000) }
  | 1 => { reLo := 9946456249858 / 10000000000000, reHi := 994645624990002 / 1000000000000000, imLo := 103344475862844 / 1000000000000000, imHi := 103344475867047 / 1000000000000000 }
  | 2 => { reLo := 978639838611158 / 1000000000000000, reHi := 978639838620386 / 1000000000000000, imLo := 205582261566856 / 1000000000000000, imHi := 205582261576087 / 1000000000000000 }
  | 3 => { reLo := 915471867442134 / 1000000000000000, reHi := 915471867463992 / 1000000000000000, imLo := 402381982562209 / 1000000000000000, imHi := 402381982584072 / 1000000000000000 }
  | 4 => { reLo := 676177480169699 / 1000000000000000, reHi := 676177480227316 / 1000000000000000, imLo := 736738770002587 / 1000000000000000, imHi := 736738770060208 / 1000000000000000 }
  | 5 => { reLo := -(85568030621185 / 1000000000000000), reHi := -(85568030458362 / 1000000000000000), imLo := 996332330087345 / 1000000000000000, imHi := 996332330250167 / 1000000000000000 }
  | 6 => { reLo := -(985356224465205 / 1000000000000000), reHi := -(985356224112890 / 1000000000000000), imLo := -(170508390687446 / 1000000000000000), imHi := -(170508390335129 / 1000000000000000) }
  | 7 => { reLo := 941853777103189 / 1000000000000000, reHi := 941853777917647 / 1000000000000000, imLo := 336023007360378 / 1000000000000000, imHi := 336023008174840 / 1000000000000000 }
  | 8 => { reLo := 774177075420675 / 1000000000000000, reHi := 774177077502232 / 1000000000000000, imLo := 632969077351889 / 1000000000000000, imHi := 632969079433451 / 1000000000000000 }
  | _ => { reLo := 198700288588079 / 1000000000000000, reHi := 198700294446196 / 1000000000000000, imLo := 980060298272016 / 1000000000000000, imHi := 980060304130135 / 1000000000000000 }

theorem record2680_cell17168_family10_tight_base_mem3256 :
    (record2680Cell17168Family10TightStageBox3256 0).Mem
      (Complex.exp (((capturedModulations2584 10 *
        record2680Center3212 17168 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell17168_phase_scaled5123245 (family := (10 : Fin 30))
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676
    (inner := phaseRect3218
      (capturedModulations2584 10 * record2680Center3212 17168)) ?_ ?_ ?_ ?_ hphase
  all_goals
    norm_num [record2680Cell17168Family10TightStageBox3256,
      phaseRect3218, phaseTaylorError3218, reExpIPartial2676,
      imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584,
      record2680Center3212, record2680Grid3212, diagnosticRadius3201,
      Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_10,
      Fin.ext_iff, binary64Value2674, binary64ExponentBits2674,
      binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

set_option maxRecDepth 100000 in
theorem record2680_cell17168_family10_tight_step_mem3256
    {stage : ℕ} (hstage : stage < 9) {w : ℂ}
    (hw : (record2680Cell17168Family10TightStageBox3256 stage).Mem w) :
    (record2680Cell17168Family10TightStageBox3256 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676
    (inner := (record2680Cell17168Family10TightStageBox3256 stage).mul
      (record2680Cell17168Family10TightStageBox3256 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals
    interval_cases stage <;>
      norm_num [record2680Cell17168Family10TightStageBox3256,
        ComplexRect2427.mul, RealInterval2429.mul,
        RealInterval2429.add, RealInterval2429.sub]

theorem record2680_cell17168_family10_tight_phase_box_mem3256 :
    (record2680Cell17168Family10TightStageBox3256 9).Mem
      (Complex.exp (((capturedModulations2584 10 *
        record2680Center3212 17168 : ℝ) : ℂ) * Complex.I)) := by
  have hstage :
      (record2680Cell17168Family10TightStageBox3256 9).Mem
        ((Complex.exp (((capturedModulations2584 10 *
          record2680Center3212 17168 / 512 : ℝ) : ℂ) * Complex.I)) ^ (2 ^ 9)) := by
    apply complexRectPowSq_staged_mem_of_bound3251
      record2680_cell17168_family10_tight_base_mem3256
    intro stage hstage w hw
    exact record2680_cell17168_family10_tight_step_mem3256 hstage hw
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num] at hstage
  rw [complex_phase_eq_pow512_3218]
  exact hstage

end ConnesWeilRH.Dev
