import ConnesWeilRH.Dev.C1RouteAConcreteOwnerWeightedMiddlePoint3239
import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem weighted_owner_taxi_ball_mem_of_component_balls3241
    {sigma x : ℝ}
    {weightBall aggregateBall : ComplexTaxiBall3235}
    (hweight : weightBall.Mem ((Real.exp (sigma * x) : ℝ) : ℂ))
    (haggregate : aggregateBall.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x)) :
    (weightBall.mul aggregateBall).Mem
      (weightedFunction2348 sigma
        (externalPhysical2344 record2680CorrectionCoefficient
          capturedModulations2584) x) := by
  unfold weightedFunction2348 weightedExp2348
  simpa using ComplexTaxiBall3235.mem_mul hweight haggregate

theorem weighted_owner_value_upper_of_component_balls3241
    {sigma x : ℝ}
    {weightBall aggregateBall : ComplexTaxiBall3235}
    (hweight : weightBall.Mem ((Real.exp (sigma * x) : ℝ) : ℂ))
    (haggregate : aggregateBall.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x)) :
    weightedExternal3201 sigma record2680CorrectionCoefficient
      capturedModulations2584 x ≤
      (weightBall.mul aggregateBall).center.re +
        (weightBall.mul aggregateBall).radius := by
  have hmem := weighted_owner_taxi_ball_mem_of_component_balls3241
    (sigma := sigma) (x := x) hweight haggregate
  have hupper := taxi_ball_real_upper3239 hmem
  change Real.exp (sigma * x) *
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x).re ≤
    (weightBall.mul aggregateBall).center.re +
      (weightBall.mul aggregateBall).radius
  change (((Real.exp (sigma * x) : ℝ) : ℂ) *
      externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x).re ≤
    (weightBall.mul aggregateBall).center.re +
      (weightBall.mul aggregateBall).radius at hupper
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, zero_mul, sub_zero] using hupper

end ConnesWeilRH.Dev

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2680_middle_point_weighted_value_upper_via_bridge3241 :
    weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584 (record2680Center3212 17168) ≤
      record2680MiddlePointWeightedAggregateBall3239.center.re +
        record2680MiddlePointWeightedAggregateBall3239.radius := by
  simpa [record2680MiddlePointWeightedAggregateBall3239] using
    (weighted_owner_value_upper_of_component_balls3241
      (sigma := -1 / 2) (x := record2680Center3212 17168)
      record2680_middle_point_weight_ball_mem3239
      record2680_middle_point_aggregate_ball_mem3236)
end ConnesWeilRH.Dev
namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def weighted_owner_family_ball3241
    (bumpBall phaseBall : Fin 30 → ComplexTaxiBall3235)
    (family : Fin 30) : ComplexTaxiBall3235 :=
  (ComplexTaxiBall3235.point (record2680CorrectionCoefficient family)).mul
    (bumpBall family) |>.mul (phaseBall family)

noncomputable def weighted_owner_aggregate_ball3241
    (bumpBall phaseBall : Fin 30 → ComplexTaxiBall3235) :
    ComplexTaxiBall3235 :=
  ComplexTaxiBall3235.sumFinset
    (weighted_owner_family_ball3241 bumpBall phaseBall) Finset.univ

theorem weighted_owner_aggregate_ball_mem_of_component_balls3241
    {x : ℝ}
    (bumpBall phaseBall : Fin 30 → ComplexTaxiBall3235)
    (hbump : ∀ family,
      (bumpBall family).Mem
        (widthBump (storedWidth family ^ 2) x : ℂ))
    (hphase : ∀ family,
      (phaseBall family).Mem
        (Complex.exp (((capturedModulations2584 family * x : ℝ) : ℂ) *
          Complex.I))) :
    (weighted_owner_aggregate_ball3241 bumpBall phaseBall).Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x) := by
  unfold weighted_owner_aggregate_ball3241
  apply ComplexTaxiBall3235.mem_sumFinset
  intro family _
  unfold weighted_owner_family_ball3241
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexTaxiBall3235.mem_mul
    (ComplexTaxiBall3235.mem_mul
      (ComplexTaxiBall3235.point_mem _)
      (hbump family))
    (hphase family)

end ConnesWeilRH.Dev

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem weighted_owner_value_upper_of_component_members3241
    {sigma x : ℝ}
    (weightBall : ComplexTaxiBall3235)
    (bumpBall phaseBall : Fin 30 → ComplexTaxiBall3235)
    (hweight : weightBall.Mem ((Real.exp (sigma * x) : ℝ) : ℂ))
    (hbump : ∀ family,
      (bumpBall family).Mem
        (widthBump (storedWidth family ^ 2) x : ℂ))
    (hphase : ∀ family,
      (phaseBall family).Mem
        (Complex.exp (((capturedModulations2584 family * x : ℝ) : ℂ) *
          Complex.I))) :
    weightedExternal3201 sigma record2680CorrectionCoefficient
      capturedModulations2584 x ≤
      (weightBall.mul
        (weighted_owner_aggregate_ball3241 bumpBall phaseBall)).center.re +
      (weightBall.mul
        (weighted_owner_aggregate_ball3241 bumpBall phaseBall)).radius := by
  apply weighted_owner_value_upper_of_component_balls3241 hweight
  exact weighted_owner_aggregate_ball_mem_of_component_balls3241
    bumpBall phaseBall hbump hphase

end ConnesWeilRH.Dev

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def weighted_owner_phase_ball3241
    (family : Fin 30) (x : ℝ) : ComplexTaxiBall3235 :=
  record2680MiddlePointPhaseBall3236
    (capturedModulations2584 family * x) 9

theorem weighted_owner_phase_ball_mem3241
    {family : Fin 30} {x : ℝ}
    (hscaled :
      |(capturedModulations2584 family * x) / 512| ≤ 1) :
    (weighted_owner_phase_ball3241 family x).Mem
      (Complex.exp (((capturedModulations2584 family * x : ℝ) : ℂ) *
        Complex.I)) := by
  have hphase := record2680_middle_point_phase_ball_mem3236 hscaled 9
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hphase
  rw [complex_phase_eq_pow512_3218]
  exact hphase

end ConnesWeilRH.Dev

namespace ConnesWeilRH.Dev

noncomputable def weighted_owner_weight_argument3241
    (sigma x : ℝ) : ℝ := sigma * x

noncomputable def weighted_owner_weight_taylor_sum3241
    (sigma x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 30,
    weighted_owner_weight_argument3241 sigma x ^ m / (m.factorial : ℝ)

noncomputable def weighted_owner_weight_taylor_error3241
    (sigma x : ℝ) : ℝ :=
  |weighted_owner_weight_argument3241 sigma x| ^ 30 *
    ((30 : ℕ).succ / ((30 : ℕ).factorial * 30))

noncomputable def weighted_owner_weight_lower3241
    (sigma x : ℝ) : ℝ :=
  weighted_owner_weight_taylor_sum3241 sigma x -
    weighted_owner_weight_taylor_error3241 sigma x

noncomputable def weighted_owner_weight_upper3241
    (sigma x : ℝ) : ℝ :=
  weighted_owner_weight_taylor_sum3241 sigma x +
    weighted_owner_weight_taylor_error3241 sigma x

noncomputable def weighted_owner_weight_ball3241
    (sigma x : ℝ) : ComplexTaxiBall3235 :=
  { center :=
      (((weighted_owner_weight_lower3241 sigma x +
        weighted_owner_weight_upper3241 sigma x) / 2 : ℝ) : ℂ)
    radius :=
      (weighted_owner_weight_upper3241 sigma x -
        weighted_owner_weight_lower3241 sigma x) / 2 }

theorem weighted_owner_weight_ball_mem3241
    {sigma x : ℝ}
    (harg : |weighted_owner_weight_argument3241 sigma x| ≤ 1) :
    (weighted_owner_weight_ball3241 sigma x).Mem
      ((Real.exp (sigma * x) : ℝ) : ℂ) := by
  have hTaylor := expTwoSided2676 (n := 30) (by norm_num)
    harg
    (S := weighted_owner_weight_taylor_sum3241 sigma x)
    (E := weighted_owner_weight_taylor_error3241 sigma x) rfl rfl
  have hTaylor' :
    weighted_owner_weight_lower3241 sigma x ≤ Real.exp (sigma * x) ∧
      Real.exp (sigma * x) ≤ weighted_owner_weight_upper3241 sigma x := by
    simpa [weighted_owner_weight_argument3241,
      weighted_owner_weight_lower3241, weighted_owner_weight_upper3241,
      weighted_owner_weight_taylor_sum3241, weighted_owner_weight_taylor_error3241] using hTaylor
  dsimp [weighted_owner_weight_lower3241, weighted_owner_weight_upper3241] at hTaylor'
  have herror : 0 ≤ weighted_owner_weight_taylor_error3241 sigma x := by
    dsimp [weighted_owner_weight_taylor_error3241]
    positivity
  constructor
  · change 0 ≤
      (weighted_owner_weight_upper3241 sigma x -
        weighted_owner_weight_lower3241 sigma x) / 2
    dsimp [weighted_owner_weight_upper3241,
      weighted_owner_weight_lower3241]
    linarith
  · change taxiNorm3235
        (((Real.exp (sigma * x) : ℝ) : ℂ) -
          (((weighted_owner_weight_lower3241 sigma x +
            weighted_owner_weight_upper3241 sigma x) / 2 : ℝ) : ℂ)) ≤
      (weighted_owner_weight_upper3241 sigma x -
        weighted_owner_weight_lower3241 sigma x) / 2
    simp only [taxiNorm3235, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_self, abs_zero, add_zero,
      weighted_owner_weight_upper3241, weighted_owner_weight_lower3241, weighted_owner_weight_argument3241]
    rw [abs_le]
    constructor <;> linarith [hTaylor'.1, hTaylor'.2]

end ConnesWeilRH.Dev