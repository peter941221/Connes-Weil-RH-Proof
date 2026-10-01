import ConnesWeilRH.Dev.C1RouteAWeightedChordPanel

namespace ConnesWeilRH.Dev

/-!
The numerical producer is evaluated on the stored `linspace` coordinates,
whereas `stripNorm_le_nodeUpper2348` consumes the exact affine grid.  This
file keeps that conversion explicit: an analytic coordinate-transfer estimate
and a separately booked charge imply the node bounds required by the panel
theorem.  No numerical value is imported here.
-/

theorem norm_value_le_of_deriv_bound2359
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {a b C : ℝ}
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (f' x) (Set.Icc a b) x)
    (hbound : ∀ x ∈ Set.Ico a b, ‖f' x‖ ≤ C) :
    ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ ‖f a‖ + C * (x - a) := by
  have hnormdiff : ∀ x ∈ Set.Icc a b, ‖f x - f a‖ ≤ C * (x - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
  intro x hx
  calc
    ‖f x‖ = ‖(f x - f a) + f a‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x - f a‖ + ‖f a‖ := norm_add_le _ _
    _ ≤ C * (x - a) + ‖f a‖ := add_le_add_right (hnormdiff x hx) _
    _ = ‖f a‖ + C * (x - a) := by ring

theorem weightedFunction2348_norm_le_of_coordinate_segment2359
    (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    (radius a b zeroBound firstBound : ℝ)
    (hradius : ∀ x ∈ Set.Icc a b, |x| ≤ radius)
    (hzeroBound : 0 ≤ zeroBound) (hfirstBound : 0 ≤ firstBound)
    (hzero : ∀ x ∈ Set.Icc a b, ‖function x‖ ≤ zeroBound)
    (hfirst : ∀ x ∈ Set.Icc a b, ‖deriv function x‖ ≤ firstBound) :
    ∀ x ∈ Set.Icc a b,
      ‖weightedFunction2348 sigma function x‖ ≤
        ‖weightedFunction2348 sigma function a‖ +
          Real.exp (|sigma| * radius) * (|sigma| * zeroBound + firstBound) * (x - a) := by
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (weightedFunction2348 sigma function)
        (weightedFirst2348 sigma function x) (Set.Icc a b) x := by
    intro x hx
    have hfunction := (hsmooth.differentiable (by decide) x).hasDerivAt
    have hpoint := (weightedExp2348_hasDerivAt sigma x).mul hfunction
    have hpoint' : HasDerivAt (weightedFunction2348 sigma function)
        (weightedFirst2348 sigma function x) x := by
      convert hpoint using 1
      dsimp [weightedFunction2348, weightedFirst2348]
      ring
    exact hpoint'.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico a b,
      ‖weightedFirst2348 sigma function x‖ ≤
        Real.exp (|sigma| * radius) * (|sigma| * zeroBound + firstBound) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := Set.Ico_subset_Icc_self hx
    rw [weightedFirst2348, norm_mul]
    have hexpNorm : ‖weightedExp2348 sigma x‖ = Real.exp (sigma * x) := by
      simp only [weightedExp2348, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    rw [hexpNorm]
    have hphase : sigma * x ≤ |sigma| * radius := by
      calc sigma * x ≤ |sigma * x| := le_abs_self _
           _ = |sigma| * |x| := abs_mul _ _
           _ ≤ |sigma| * radius := mul_le_mul_of_nonneg_left
             (hradius x hxIcc) (abs_nonneg sigma)
    have hnormZero : ‖(sigma : ℂ) * function x‖ ≤ |sigma| * zeroBound := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (le_abs_self sigma) (hzero x hxIcc)
        (norm_nonneg _) hzeroBound
    have hnorm : ‖(sigma : ℂ) * function x + deriv function x‖ ≤
        |sigma| * zeroBound + firstBound :=
      (norm_add_le _ _).trans (add_le_add (hnormZero.trans_eq (by ring))
        (hfirst x hxIcc))
    exact mul_le_mul (Real.exp_le_exp.mpr hphase) hnorm
      (Real.exp_nonneg _) (by positivity)
  exact norm_value_le_of_deriv_bound2359 hderiv hbound

theorem nodeUpper_of_coordinate_charge2359
    {cells : ℕ} {actualValue idealValue nodeUpper finalUpper charge : ℕ → ℝ}
    (hactual : ∀ index ≤ cells, actualValue index ≤ nodeUpper index)
    (hideal : ∀ index ≤ cells, idealValue index ≤ actualValue index + charge index)
    (hfinal : ∀ index ≤ cells, nodeUpper index + charge index ≤ finalUpper index) :
    ∀ index ≤ cells, idealValue index ≤ finalUpper index := by
  intro index hindex
  exact (hideal index hindex).trans ((add_le_add_right (hactual index hindex) _).trans
    (hfinal index hindex))

theorem nodeUpper_of_lipschitz_coordinate_charge2359
    {cells : ℕ} {actualValue idealValue nodeUpper finalUpper actualCoord idealCoord : ℕ → ℝ}
    {lipschitz delta : ℝ}
    (hlipschitz : 0 ≤ lipschitz)
    (hcoord : ∀ index ≤ cells, |idealCoord index - actualCoord index| ≤ delta)
    (hactual : ∀ index ≤ cells, actualValue index ≤ nodeUpper index)
    (hideal : ∀ index ≤ cells,
      idealValue index ≤ actualValue index + lipschitz * |idealCoord index - actualCoord index|)
    (hfinal : ∀ index ≤ cells, nodeUpper index + lipschitz * delta ≤ finalUpper index) :
    ∀ index ≤ cells, idealValue index ≤ finalUpper index := by
  apply nodeUpper_of_coordinate_charge2359 hactual
  · intro index hindex
    exact (hideal index hindex).trans_le (add_le_add_left
      (mul_le_mul_of_nonneg_left (hcoord index hindex) hlipschitz) _)
  · exact hfinal

end ConnesWeilRH.Dev
