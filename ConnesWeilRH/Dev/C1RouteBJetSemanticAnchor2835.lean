import ConnesWeilRH.Dev.C1SeedJetSemantics2731

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_phase_python_form2835 (x : ℝ) :
    transitionPhase2731 x = (1 - x)⁻¹ - x⁻¹ := by
  unfold transitionPhase2731
  ring

theorem routeB_quotient_python_form2835 {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    Real.smoothTransition x =
      Real.exp (transitionPhase2731 x) /
        (1 + Real.exp (transitionPhase2731 x)) := by
  rw [smoothTransition_eq_exp_mul_reciprocal2731 hx0 hx1]
  simp [transitionReciprocal2731, transitionExp2731, div_eq_mul_inv]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
