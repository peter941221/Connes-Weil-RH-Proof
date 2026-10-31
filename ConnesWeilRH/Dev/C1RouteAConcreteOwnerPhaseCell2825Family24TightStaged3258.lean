import ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamily10TightStaged3256
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
noncomputable def record2680Cell2825Family24TightStageBox3258 (stage : ℕ) : ComplexRect2427 :=
  match stage with
  | 0 => { reLo := ((738358752505467 : ℝ) / 1000000000000000), reHi := ((738358752505468 : ℝ) / 1000000000000000), imLo := ((674408149860727 : ℝ) / 1000000000000000), imHi := ((674408149860728 : ℝ) / 1000000000000000) }
  | 1 => { reLo := ((90347294802858 : ℝ) / 1000000000000000), reHi := ((90347294802864 : ℝ) / 1000000000000000), imLo := ((995910320421371 : ℝ) / 1000000000000000), imHi := ((995910320421377 : ℝ) / 1000000000000000) }
  | 2 => { reLo := -((983674732643617 : ℝ) / 1000000000000000), reHi := -((983674732643601 : ℝ) / 1000000000000000), imLo := ((179955606632635 : ℝ) / 1000000000000000), imHi := ((179955606632651 : ℝ) / 1000000000000000) }
  | 3 => { reLo := ((935231959282933 : ℝ) / 1000000000000000), reHi := ((935231959282973 : ℝ) / 1000000000000000), imLo := -((354035566484187 : ℝ) / 1000000000000000), imHi := -((354035566484147 : ℝ) / 1000000000000000) }
  | 4 => { reLo := ((749317635328413 : ℝ) / 1000000000000000), reHi := ((749317635328519 : ℝ) / 1000000000000000), imLo := -((662210752997728 : ℝ) / 1000000000000000), imHi := -((662210752997622 : ℝ) / 1000000000000000) }
  | 5 => { reLo := ((122953837228345 : ℝ) / 1000000000000000), reHi := ((122953837228647 : ℝ) / 1000000000000000), imLo := -((992412391050752 : ℝ) / 1000000000000000), imHi := -((992412391050450 : ℝ) / 1000000000000000) }
  | 6 => { reLo := -((969764707821898 : ℝ) / 1000000000000000), reHi := -((969764707821221 : ℝ) / 1000000000000000), imLo := -((244041823185895 : ℝ) / 1000000000000000), imHi := -((244041823185218 : ℝ) / 1000000000000000) }
  | 7 => { reLo := ((880887177071681 : ℝ) / 1000000000000000), reHi := ((880887177073327 : ℝ) / 1000000000000000), imLo := ((473326294714741 : ℝ) / 1000000000000000), imHi := ((473326294716387 : ℝ) / 1000000000000000) }
  | 8 => { reLo := ((551924437459370 : ℝ) / 1000000000000000), reHi := ((551924437463831 : ℝ) / 1000000000000000), imLo := ((833894127170132 : ℝ) / 1000000000000000), imHi := ((833894127174593 : ℝ) / 1000000000000000) }
  | 9 => { reLo := -((390758830671436 : ℝ) / 1000000000000000), reHi := -((390758830659069 : ℝ) / 1000000000000000), imLo := ((920493094078093 : ℝ) / 1000000000000000), imHi := ((920493094090461 : ℝ) / 1000000000000000) }
  | _ => { reLo := -((390758830671436 : ℝ) / 1000000000000000), reHi := -((390758830659069 : ℝ) / 1000000000000000), imLo := ((920493094078093 : ℝ) / 1000000000000000), imHi := ((920493094090461 : ℝ) / 1000000000000000) }

theorem record2680_cell2825_phase_scaled512_family24_3258 : |(capturedModulations2584 24 * record2680Center3212 2825) / 512| ≤ 1 := by
  norm_num [capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_24, Fin.ext_iff]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family24_tight_base_mem3258 : (record2680Cell2825Family24TightStageBox3258 0).Mem (Complex.exp (((capturedModulations2584 24 * record2680Center3212 2825 / 512 : ℝ) : ℂ) * Complex.I)) := by
  have hscaled := record2680_cell2825_phase_scaled512_family24_3258
  have hphase := phaseRect_mem3218 hscaled
  refine rectSubset2676 (inner := phaseRect3218 (capturedModulations2584 24 * record2680Center3212 2825)) ?_ ?_ ?_ ?_ hphase
  all_goals norm_num [record2680Cell2825Family24TightStageBox3258, phaseRect3218, phaseTaylorError3218, reExpIPartial2676, imExpIPartial2676, Finset.sum_range_succ, capturedModulations2584, record2680Center3212, record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.cons_val_24, Fin.ext_iff, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem record2680_cell2825_family24_tight_step_mem3258 {stage : ℕ} (hstage : stage < 9) {w : ℂ} (hw : (record2680Cell2825Family24TightStageBox3258 stage).Mem w) : (record2680Cell2825Family24TightStageBox3258 (stage + 1)).Mem (w * w) := by
  have hmul := ComplexRect2427.mem_mul hw hw
  refine rectSubset2676 (inner := (record2680Cell2825Family24TightStageBox3258 stage).mul (record2680Cell2825Family24TightStageBox3258 stage)) ?_ ?_ ?_ ?_ hmul
  all_goals interval_cases stage <;> norm_num [record2680Cell2825Family24TightStageBox3258, ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub]
theorem record2680_cell2825_family24_tight_phase_box_mem3258 : (record2680Cell2825Family24TightStageBox3258 9).Mem (Complex.exp (((capturedModulations2584 24 * record2680Center3212 2825 : ℝ) : ℂ) * Complex.I)) := by
  have hstage := complexRectPowSq_staged_mem_of_bound3251 record2680_cell2825_family24_tight_base_mem3258 (fun stage hstage w hw => record2680_cell2825_family24_tight_step_mem3258 hstage hw)
  rw [complex_phase_eq_pow512_3218]
  exact hstage
end ConnesWeilRH.Dev
