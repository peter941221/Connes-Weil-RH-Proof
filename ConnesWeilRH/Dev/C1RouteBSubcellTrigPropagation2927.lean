import ConnesWeilRH.Dev.C1RouteBAngleShift2926
import ConnesWeilRH.Dev.C1RouteBTrigTaylor2916

namespace ConnesWeilRH.Dev

theorem routeBSubcellTrigPropagation2927 {θ : ℝ}
    (hθ : (107 : ℝ) * Real.pi / 64 ≤ θ)
    (hθ' : θ ≤ (107 : ℝ) * Real.pi / 64 + Real.pi / 1024)
    (hsL : (-867 : ℝ) / 1000 < Real.sin ((52523502177204355 : ℝ) / 10 ^ 16))
    (hsR : Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) < (-853 : ℝ) / 1000)
    (hcL : (513 : ℝ) / 1000 < Real.cos ((52523502177204355 : ℝ) / 10 ^ 16))
    (hcR : Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) < (519 : ℝ) / 1000) :
    (-867 : ℝ) / 1000 < Real.sin θ ∧ Real.sin θ < (-853 : ℝ) / 1000 ∧
      (513 : ℝ) / 1000 < Real.cos θ ∧ Real.cos θ < (519 : ℝ) / 1000 := by
  let a : ℝ := (107 : ℝ) * Real.pi / 64 - 2 * Real.pi
  let b : ℝ := (107 : ℝ) * Real.pi / 64 + Real.pi / 1024 - 2 * Real.pi
  have hshift := routeBLocalAngleShiftInterval2926 hθ hθ'
  have hs := routeB_sin_bounds_of_endpoint2911 (a := a) (b := b)
    (by dsimp [a]; linarith [Real.pi_pos])
    (by dsimp [b]; linarith [Real.pi_pos]) hshift.1.le hshift.2.le
  have hc := routeB_cos_bounds_of_endpoint2911 (a := -b) (b := -a)
    (by dsimp [b]; linarith [Real.pi_pos])
    (by dsimp [a]; linarith [Real.pi_pos]) (by linarith) (by linarith)
  rw [Real.sin_sub_two_pi, Real.cos_sub_two_pi, Real.cos_neg] at hs hc
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end ConnesWeilRH.Dev
