import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace ConnesWeilRH.Dev

def routeBSinTaylor20 (x : ℝ) : ℝ :=
  ∑ j in Finset.range 21, (-1 : ℝ) ^ j * x ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ)

def routeBCosTaylor20 (x : ℝ) : ℝ :=
  ∑ j in Finset.range 21, (-1 : ℝ) ^ j * x ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)

theorem routeBTrigTaylor20_left_arithmetic2916 :
    let x : ℝ := (52523502177204355 : ℝ) / 10 ^ 16
    (-866 : ℝ) / 1000 < routeBSinTaylor20 x ∧
      routeBSinTaylor20 x < (-865 : ℝ) / 1000 ∧
      (514 : ℝ) / 1000 < routeBCosTaylor20 x ∧
      routeBCosTaylor20 x < (515 : ℝ) / 1000 := by
  norm_num [routeBSinTaylor20, routeBCosTaylor20]

theorem routeBTrigTaylor20_left_of_remainder2917
    (hsinErr hcosErr : ℝ)
    (hsinErr_nonneg : 0 ≤ hsinErr) (hcosErr_nonneg : 0 ≤ hcosErr)
    (hsinErr_small : hsinErr ≤ (1 : ℝ) / 10 ^ 20)
    (hcosErr_small : hcosErr ≤ (1 : ℝ) / 10 ^ 20)
    (hsin : |Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) -
      routeBSinTaylor20 ((52523502177204355 : ℝ) / 10 ^ 16)| ≤ hsinErr)
    (hcos : |Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) -
      routeBCosTaylor20 ((52523502177204355 : ℝ) / 10 ^ 16)| ≤ hcosErr) :
    (-867 : ℝ) / 1000 < Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) ∧
      Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) < (-864 : ℝ) / 1000 ∧
      (513 : ℝ) / 1000 < Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) ∧
      Real.cos ((52523502177204355 : ℝ) / 10 ^ 16) < (516 : ℝ) / 1000 := by
  have harith := routeBTrigTaylor20_left_arithmetic2916
  rcases harith with ⟨hslo, hshi, hclo, hchi⟩
  rw [abs_le] at hsin hcos
  constructor <;> constructor
  · linarith
  · linarith
  · linarith
  · linarith

theorem routeBSinTaylor20_eq_mathlib2919 {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.sin 20 (Set.Icc 0 x) 0 x = routeBSinTaylor20 x := by
  rw [taylor_within_apply]
  simp_rw [Real.iteratedDerivWithin_sin_Icc _ hx]
  simp [routeBSinTaylor20, Real.iteratedDeriv_even_sin,
    Real.iteratedDeriv_odd_sin, smul_eq_mul, div_eq_mul_inv]

theorem routeBSinEndpoint_of_mathlibRemainder2923
    (hsinErr : 0 ≤ (1 : ℝ) / 10 ^ 20)
    (hrem : ‖Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) -
      taylorWithinEval Real.sin 20
        (Set.Icc 0 ((52523502177204355 : ℝ) / 10 ^ 16)) 0
        ((52523502177204355 : ℝ) / 10 ^ 16)‖ ≤ hsinErr) :
    (-867 : ℝ) / 1000 <
        Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) ∧
      Real.sin ((52523502177204355 : ℝ) / 10 ^ 16) < (-864 : ℝ) / 1000 := by
  have hpoly := routeBSinTaylor20_eq_mathlib2919
    (x := (52523502177204355 : ℝ) / 10 ^ 16) (by norm_num)
  rw [hpoly] at hrem
  have h := routeBTrigTaylor20_left_of_remainder2917
    (1 / 10 ^ 20) (1 / 10 ^ 20) (by positivity) (by positivity)
    (by rfl) (by rfl) (by simpa [Real.norm_eq_abs] using hrem)
  exact h.1.trans h.2.1

end ConnesWeilRH.Dev
