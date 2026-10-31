import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell16923Bump3242

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell16923BumpBall3242
    (family : Fin 30) : ComplexTaxiBall3235 :=
  { center :=
      (((record2680Cell16923BumpInterval3242 family).lo +
        (record2680Cell16923BumpInterval3242 family).hi) / 2 : ℝ)
    radius :=
      ((record2680Cell16923BumpInterval3242 family).hi -
        (record2680Cell16923BumpInterval3242 family).lo) / 2 }

theorem record2680_cell16923_bump_ball_mem3242
    (family : Fin 30) :
    (record2680Cell16923BumpBall3242 family).Mem
      (widthBump (storedWidth family ^ 2)
        (record2680Center3212 16923) : ℂ) := by
  have h := record2680_cell16923_bump_mem3242 (family := family)
  unfold record2680Cell16923BumpBall3242
  constructor
  · change 0 ≤
      ((record2680Cell16923BumpInterval3242 family).hi -
        (record2680Cell16923BumpInterval3242 family).lo) / 2
    linarith [h.1, h.2]
  · simp [record2680Cell16923BumpBall3242, taxiNorm3235,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]

theorem record2680_cell16923_phase_scaled5123242
    {family : Fin 30} :
    |(capturedModulations2584 family * record2680Center3212 16923) / 512| ≤ 1 := by
  fin_cases family <;>
    norm_num [capturedModulations2584, record2680Center3212,
      record2680Grid3212, diagnosticRadius3201, Matrix.cons_val_zero,
      Matrix.cons_val_four, Fin.ext_iff]

theorem record2680_cell16923_weight_argument_bound3242 :
    |weighted_owner_weight_argument3241 (-1 / 2)
      (record2680Center3212 16923)| ≤ 1 := by
  norm_num [weighted_owner_weight_argument3241, record2680Center3212,
    record2680Grid3212, diagnosticRadius3201]

noncomputable def record2680Cell16923BumpBalls3242 :
    Fin 30 → ComplexTaxiBall3235 :=
  record2680Cell16923BumpBall3242

noncomputable def record2680Cell16923PhaseBalls3242 :
    Fin 30 → ComplexTaxiBall3235 :=
  fun family => weighted_owner_phase_ball3241 family
    (record2680Center3212 16923)

noncomputable def record2680Cell16923WeightBall3242 : ComplexTaxiBall3235 :=
  weighted_owner_weight_ball3241 (-1 / 2) (record2680Center3212 16923)

theorem record2680_cell16923_value_upper3242 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 16923) ≤
      (record2680Cell16923WeightBall3242.mul
        (weighted_owner_aggregate_ball3241
          record2680Cell16923BumpBalls3242
          record2680Cell16923PhaseBalls3242)).center.re +
      (record2680Cell16923WeightBall3242.mul
        (weighted_owner_aggregate_ball3241
          record2680Cell16923BumpBalls3242
          record2680Cell16923PhaseBalls3242)).radius := by
  apply weighted_owner_value_upper_of_component_members3241
  · exact weighted_owner_weight_ball_mem3241
      record2680_cell16923_weight_argument_bound3242
  · intro family
    exact record2680_cell16923_bump_ball_mem3242 family
  · intro family
    exact weighted_owner_phase_ball_mem3241
      (record2680_cell16923_phase_scaled5123242 (family := family))

end ConnesWeilRH.Dev