import ConnesWeilRH.Dev.C1RouteBTrigTaylor2916
import Mathlib.Analysis.Calculus.Taylor

namespace ConnesWeilRH.Dev

theorem routeBCosTaylor20_eq_mathlib2922 {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.cos 20 (Set.Icc 0 x) 0 x = routeBCosTaylor20 x := by
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_cos_Icc _ hx]
  simp [routeBCosTaylor20, Real.iteratedDeriv_even_cos,
    Real.iteratedDeriv_odd_cos, smul_eq_mul, div_eq_mul_inv]

end ConnesWeilRH.Dev
