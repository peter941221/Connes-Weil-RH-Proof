import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace StirlingGammaProject

noncomputable section

/-- The critical Mellin integrand at s = 1 + I/2. -/
def ellIntegrand (x : ℝ) : ℂ :=
  (Real.exp (-x) : ℂ) * (x : ℂ) ^ (Complex.I / 2)

/-- s = 1 + I/2 lies in the right half-plane. -/
lemma re_one_half_i_pos : 0 < ((1 : ℂ) + Complex.I / 2).re := by
  norm_num

/-- Gamma(1 + I/2) equals its Euler integral. -/
theorem gamma_at_one_half_i_eq_integral :
    Complex.Gamma (1 + Complex.I / 2) =
      Complex.GammaIntegral (1 + Complex.I / 2) := by
  exact Complex.Gamma_eq_integral re_one_half_i_pos

/-- Norm of the critical integrand: the cpow unit-disk factor has norm 1. -/
lemma integrand_norm_eq_exp_neg (u : ℝ) (hu : 0 < u) :
    ‖ellIntegrand u‖ = Real.exp (-u) := by
  unfold ellIntegrand
  rw [norm_mul]
  rw [Complex.norm_of_nonneg (Real.exp_pos (-u)).le]
  have hc : ‖(u : ℂ) ^ (Complex.I / 2)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu (Complex.I / 2)]
    simp [Complex.I]
  rw [hc, mul_one]

/-- Tail norm bound: the tail integral of the critical integrand decays like exp (-a).
Needed by the downstream split (docs/886) to control the oscillatory part away from
the origin. Here a plays the role of the split point. -/
theorem ell_tail_norm_bound (a : ℝ) (ha : 0 ≤ a) :
    ‖∫ x in Set.Ioi a, ellIntegrand x‖ ≤ Real.exp (-a) := by
  calc
    ‖∫ x in Set.Ioi a, ellIntegrand x‖ ≤
        (∫ x in Set.Ioi a, ‖ellIntegrand x‖ : ℝ) := by
      simpa using (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict (Set.Ioi a)) (f := ellIntegrand))
    _ = Real.exp (-a) := by
      have h : (∫ x in Set.Ioi a, ‖ellIntegrand x‖ : ℝ) =
          (∫ x in Set.Ioi a, Real.exp (-x) : ℝ) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
          integrand_norm_eq_exp_neg x (lt_of_le_of_lt ha (Set.mem_Ioi.mp hx)))
      rw [h, integral_exp_neg_Ioi]


end

end StirlingGammaProject
end Dev
end Source
end ConnesWeilRH
