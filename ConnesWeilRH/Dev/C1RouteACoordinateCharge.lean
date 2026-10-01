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
