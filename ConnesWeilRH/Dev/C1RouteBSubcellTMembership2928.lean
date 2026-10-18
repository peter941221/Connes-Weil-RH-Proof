import ConnesWeilRH.Dev.C1RouteBSubcellTrigPropagation2927
import ConnesWeilRH.Dev.C1RouteBLocalStageT2910

namespace ConnesWeilRH.Dev

theorem routeBSubcellTMembership2928 {θ : ℝ}
    (hθ : (107 : ℝ) * Real.pi / 64 ≤ θ)
    (hθ' : θ ≤ (107 : ℝ) * Real.pi / 64 + Real.pi / 1024)
    (hsL : (-867 : ℝ) / 1000 < Real.sin ((52523502177204355 : ℝ) / 10 ^ 16))
    (hsR : Real.sin ((52554181792962067 : ℝ) / 10 ^ 16) < (-853 : ℝ) / 1000)
    (hcL : (513 : ℝ) / 1000 < Real.cos ((52523502177204355 : ℝ) / 10 ^ 16))
    (hcR : Real.cos ((52554181792962067 : ℝ) / 10 ^ 16) < (519 : ℝ) / 1000) :
    ComplexRect2427.Mem
      ((1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ))
      routeBLocalStageTRect2910 := by
  have htrig := routeBSubcellTrigPropagation2927 hθ hθ' hsL hsR hcL hcR
  apply routeBLocalStageT_mem_of_trig_bounds2910 θ
  · linarith
  · linarith
  · linarith
  · linarith

end ConnesWeilRH.Dev
