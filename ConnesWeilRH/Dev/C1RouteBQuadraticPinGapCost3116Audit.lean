import ConnesWeilRH.Dev.C1RouteBQuadraticPinGapCost3116

open ConnesWeilRH.Source.C1RouteBQuadraticPinGapCost3116

namespace ConnesWeilRH.Source.C1RouteBQuadraticPinGapCost3116

theorem opposite_targets_reject_critical_line3116 (F : ℂ → ℂ) (rho : ℂ)
    (hline : rho.re = 1 / 2) (hone : F rho = 1) (hminus : F (1 - star rho) = -1) :
    False := by
  have heq : 1 - star rho = rho := by
    apply Complex.ext
    · simp
      linarith
    · simp
  rw [heq, hone] at hminus
  norm_num at hminus

theorem reject_zero_height_guard3116 : ¬(1 : ℝ) ≤ |(0 : ℝ)| := by norm_num

theorem tiny_point_within_rowB_caps3116 :
    ‖tinyGapPoint3116‖ ≤ ConnesWeilRH.Source.C1FourPointRowBWired2721.wiredRhoNormCapRowB2721 ∧
      |tinyGapPoint3116.im| ≤ ConnesWeilRH.Source.C1FourPointRowBWired2721.wiredRhoImCapRowB2721 := by
  constructor
  · calc ‖tinyGapPoint3116‖ ≤
        ‖(((1 / 2 : ℝ) + 1 / 10 ^ 12 : ℝ) : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
         _ ≤ _ := by norm_num [ConnesWeilRH.Source.C1FourPointRowBWired2721.wiredRhoNormCapRowB2721]
  · norm_num [tinyGapPoint3116,
      ConnesWeilRH.Source.C1FourPointRowBWired2721.wiredRhoImCapRowB2721]

end ConnesWeilRH.Source.C1RouteBQuadraticPinGapCost3116

#check powered_correction_cardinal_pin_cost3116
#check powered_correction_fixed_pin_gap_floor3116

#print axioms analytic_opposite_targets_quadratic_cost3116
#print axioms quadratic_pin_im_square3116
#print axioms quadratic_pin_gap_cost3116
#print axioms powered_correction_pin_gap_cost3116
#print axioms powered_correction_cardinal_pin_cost3116
#print axioms powered_correction_fixed_pin_gap_floor3116
#print axioms reject_fixed_pin_below_gap_floor3116
#print axioms tiny_gap_correction_rejects_fixed_pin3116
#print axioms opposite_targets_reject_critical_line3116
#print axioms reject_zero_height_guard3116
#print axioms tiny_point_within_rowB_caps3116
