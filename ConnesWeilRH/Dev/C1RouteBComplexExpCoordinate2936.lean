import Mathlib.Analysis.Complex.Trigonometric

namespace ConnesWeilRH.Dev

theorem routeBComplexExpReCoordinate2936 (z : ℂ) :
    (Complex.exp z).re = Real.exp z.re * Real.cos z.im := by
  exact Complex.exp_re z

theorem routeBComplexExpImCoordinate2936 (z : ℂ) :
    (Complex.exp z).im = Real.exp z.re * Real.sin z.im := by
  exact Complex.exp_im z

end ConnesWeilRH.Dev
