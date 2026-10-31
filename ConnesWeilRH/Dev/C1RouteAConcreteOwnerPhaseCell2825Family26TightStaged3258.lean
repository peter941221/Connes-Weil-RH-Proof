import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family26TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((700146595968805 : ℝ) / 1000000000000000), reHi := ((700146595968806 : ℝ) / 1000000000000000), imLo := ((713999120554986 : ℝ) / 1000000000000000), imHi := ((713999120554987 : ℝ) / 1000000000000000) }
  | 1 => { reLo := -((19589488306591 : ℝ) / 1000000000000000), reHi := -((19589488306585 : ℝ) / 1000000000000000), imLo := ((999808107562586 : ℝ) / 1000000000000000), imHi := ((999808107562592 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((999232503895779 : ℝ) / 1000000000000000), reHi := -((999232503895764 : ℝ) / 1000000000000000), imLo := -((39171458463866 : ℝ) / 1000000000000000), imHi := -((39171458463851 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((996931193683610 : ℝ) / 1000000000000000), reHi := ((996931193683644 : ℝ) / 1000000000000000), imLo := ((78282789044164 : ℝ) / 1000000000000000), imHi := ((78282789044198 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((987743609878888 : ℝ) / 1000000000000000), reHi := ((987743609878964 : ℝ) / 1000000000000000), imLo := ((156085108653360 : ℝ) / 1000000000000000), imHi := ((156085108653436 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((951274877713221 : ℝ) / 1000000000000000), reHi := ((951274877713397 : ℝ) / 1000000000000000), imLo := ((308344137339215 : ℝ) / 1000000000000000), imHi := ((308344137339392 : ℝ) / 1000000000000000) }
  | 6 => { reLo := ((809847785936728 : ℝ) / 1000000000000000), reHi := ((809847785937175 : ℝ) / 1000000000000000), imLo := ((586640063081899 : ℝ) / 1000000000000000), imHi := ((586640063082347 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((311706872773359 : ℝ) / 1000000000000000), reHi := ((311706872774611 : ℝ) / 1000000000000000), imLo := ((950178312457315 : ℝ) / 1000000000000000), imHi := ((950178312458568 : ℝ) / 1000000000000000) }
  | 8 => { reLo := -((805677650932467 : ℝ) / 1000000000000000), reHi := -((805677650929302 : ℝ) / 1000000000000000), imLo := ((592354220706273 : ℝ) / 1000000000000000), imHi := ((592354220709436 : ℝ) / 1000000000000000) }
  | 9 => { reLo := ((298232954414674 : ℝ) / 1000000000000000), reHi := ((298232954423524 : ℝ) / 1000000000000000), imLo := -((954493114122222 : ℝ) / 1000000000000000), imHi := -((954493114113373 : ℝ) / 1000000000000000) }
  | _ => { reLo := ((298232954414674 : ℝ) / 1000000000000000), reHi := ((298232954423524 : ℝ) / 1000000000000000), imLo := -((954493114122222 : ℝ) / 1000000000000000), imHi := -((954493114113373 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family26_3258 : |(capturedModulations2584 26 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_26, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family26_tight_base_mem3258 : (record2680Cell2825Family26TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 26 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family26_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 26 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family26TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_26, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family26_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family26TightStageBox3258 stage).Mem w) : (record2680Cell2825Family26TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family26TightStageBox3258 stage).mul (record2680Cell2825Family26TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family26TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family26_tight_phase_box_mem3258 : (record2680Cell2825Family26TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 26 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family26_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family26_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
