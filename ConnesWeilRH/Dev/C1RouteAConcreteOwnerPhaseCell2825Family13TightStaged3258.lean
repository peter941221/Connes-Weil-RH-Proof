import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family13TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((934691006256740 : ℝ) / 1000000000000000), reHi := ((934691006256741 : ℝ) / 1000000000000000), imLo := ((355461281749168 : ℝ) / 1000000000000000), imHi := ((355461281749169 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((747294554354474 : ℝ) / 1000000000000000), reHi := ((747294554354479 : ℝ) / 1000000000000000), imLo := ((664492926246879 : ℝ) / 1000000000000000), imHi := ((664492926246885 : ℝ) / 1000000000000000) }
  | 2 => { reLo := ((116898301935702 : ℝ) / 1000000000000000), reHi := ((116898301935721 : ℝ) / 1000000000000000), imLo := ((993143890382722 : ℝ) / 1000000000000000), imHi := ((993143890382741 : ℝ) / 1000000000000000) }
  | 3 => { reLo := -((972669574009117 : ℝ) / 1000000000000000), reHi := -((972669574009072 : ℝ) / 1000000000000000), imLo := ((232193668727113 : ℝ) / 1000000000000000), imHi := ((232193668727158 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((892172200406011 : ℝ) / 1000000000000000), reHi := ((892172200406122 : ℝ) / 1000000000000000), imLo := -((451695433696919 : ℝ) / 1000000000000000), imHi := -((451695433696808 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((591942470354654 : ℝ) / 1000000000000000), reHi := ((591942470354955 : ℝ) / 1000000000000000), imLo := -((805980217989557 : ℝ) / 1000000000000000), imHi := -((805980217989256 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((299208223580925 : ℝ) / 1000000000000000), reHi := -((299208223580080 : ℝ) / 1000000000000000), imLo := -((954187842587928 : ℝ) / 1000000000000000), imHi := -((954187842587084 : ℝ) / 1000000000000000) }
  | 7 => { reLo := -((820948877884659 : ℝ) / 1000000000000000), reHi := -((820948877882540 : ℝ) / 1000000000000000), imLo := ((571001698684379 : ℝ) / 1000000000000000), imHi := ((571001698686500 : ℝ) / 1000000000000000) }
  | 8 => { reLo := ((347914120193732 : ℝ) / 1000000000000000), reHi := ((347914120199636 : ℝ) / 1000000000000000), imLo := -((937526407613834 : ℝ) / 1000000000000000), imHi := -((937526407607929 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((757911529943124 : ℝ) / 1000000000000000), reHi := -((757911529927940 : ℝ) / 1000000000000000), imLo := -((652357350537786 : ℝ) / 1000000000000000), imHi := -((652357350522604 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((757911529943124 : ℝ) / 1000000000000000), reHi := -((757911529927940 : ℝ) / 1000000000000000), imLo := -((652357350537786 : ℝ) / 1000000000000000), imHi := -((652357350522604 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family13_3258 : |(capturedModulations2584 13 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_13, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family13_tight_base_mem3258 : (record2680Cell2825Family13TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 13 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family13_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 13 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family13TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_13, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family13_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family13TightStageBox3258 stage).Mem w) : (record2680Cell2825Family13TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family13TightStageBox3258 stage).mul (record2680Cell2825Family13TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family13TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family13_tight_phase_box_mem3258 : (record2680Cell2825Family13TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 13 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family13_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family13_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
