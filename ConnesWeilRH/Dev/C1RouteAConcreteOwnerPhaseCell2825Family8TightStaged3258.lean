import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family8TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((987862335821879 : ℝ) / 1000000000000000), reHi := ((987862335821880 : ℝ) / 1000000000000000), imLo := ((155331920301461 : ℝ) / 1000000000000000), imHi := ((155331920301462 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((951743989070918 : ℝ) / 1000000000000000), reHi := ((951743989070923 : ℝ) / 1000000000000000), imLo := ((306893107233397 : ℝ) / 1000000000000000), imHi := ((306893107233402 : ℝ) / 1000000000000000) }
  | 2 => { reLo := ((811633241465250 : ℝ) / 1000000000000000), reHi := ((811633241465265 : ℝ) / 1000000000000000), imLo := ((584167340193363 : ℝ) / 1000000000000000), imHi := ((584167340193379 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((317497037302780 : ℝ) / 1000000000000000), reHi := ((317497037302826 : ℝ) / 1000000000000000), imLo := ((948259263758544 : ℝ) / 1000000000000000), imHi := ((948259263758590 : ℝ) / 1000000000000000) }
  | 4 => { reLo := -((798391262607942 : ℝ) / 1000000000000000), reHi := -((798391262607822 : ℝ) / 1000000000000000), imLo := ((602139013676505 : ℝ) / 1000000000000000), imHi := ((602139013676624 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((274857216417053 : ℝ) / 1000000000000000), reHi := ((274857216417391 : ℝ) / 1000000000000000), imLo := -((961485054789563 : ℝ) / 1000000000000000), imHi := -((961485054789225 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((848907021167160 : ℝ) / 1000000000000000), reHi := -((848907021166321 : ℝ) / 1000000000000000), imLo := -((528542211572765 : ℝ) / 1000000000000000), imHi := -((528542211571927 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((441286261171246 : ℝ) / 1000000000000000), reHi := ((441286261173559 : ℝ) / 1000000000000000), imLo := ((897366388772366 : ℝ) / 1000000000000000), imHi := ((897366388774679 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((610532871404013 : ℝ) / 1000000000000000), reHi := -((610532871397817 : ℝ) / 1000000000000000), imLo := ((791990917204199 : ℝ) / 1000000000000000), imHi := ((791990917210394 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((254499225886499 : ℝ) / 1000000000000000), reHi := -((254499225869118 : ℝ) / 1000000000000000), imLo := -((967072977620721 : ℝ) / 1000000000000000), imHi := -((967072977603339 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((254499225886499 : ℝ) / 1000000000000000), reHi := -((254499225869118 : ℝ) / 1000000000000000), imLo := -((967072977620721 : ℝ) / 1000000000000000), imHi := -((967072977603339 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family8_3258 : |(capturedModulations2584 8 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_8, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family8_tight_base_mem3258 : (record2680Cell2825Family8TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 8 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family8_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 8 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family8TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_8, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family8_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family8TightStageBox3258 stage).Mem w) : (record2680Cell2825Family8TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family8TightStageBox3258 stage).mul (record2680Cell2825Family8TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family8TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family8_tight_phase_box_mem3258 : (record2680Cell2825Family8TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 8 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family8_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family8_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
