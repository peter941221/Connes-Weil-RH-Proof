/-
Finite-S sign: algebraic phase-window tail (Step-3 slices A3).

A1: Re[w^4] = (Re w)^4 - 6(Re w)^2(Im w)^2 + (Im w)^4.            (pure ring)
A3: reFourth_nonneg_of_cone realizes A2 as an explicit axiom-clean theorem.
The cone condition is exactly |arg| <= pi/4 on the first-quadrant cone; the
analytic content (that Gamma satisfies it on a band) is the remaining Step-3
open.  All lemmas here are axiom-clean off mathlib foundations only.

RH NOT claimed.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Finite3SignReduction

/-- The real part of the 4th complex power, in coordinates (pure ring identity). -/
theorem re_fourth_poly (w : ℂ) :
    (w ^ 4).re = w.re ^ 4 - 6 * w.re ^ 2 * w.im ^ 2 + w.im ^ 4 := by
  have hw : w ^ 4 = ((w.re : ℂ) + (w.im : ℂ) * Complex.I) ^ 4 := by
    congr 1
    exact (Complex.re_add_im w).symm
  rw [hw]
  simp [Complex.mul_re, pow_succ]
  ring_nf

/-- `(sqrt 2 - 1)^2 = 3 - 2 sqrt 2`. -/
lemma sqrt2m1_sq : (Real.sqrt 2 - 1 : ℝ) ^ 2 = 3 - 2 * Real.sqrt 2 := by
  have hs2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [hs2]

/-- Algebraic cone: `1 - 6u + u^2 >= 0` on `0 <= u <= (sqrt 2 - 1)^2`. -/
lemma cone_nonneg (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ (Real.sqrt 2 - 1 : ℝ) ^ 2) :
    0 ≤ 1 - 6 * u + u ^ 2 := by
  let r : ℝ := Real.sqrt 2
  have hs2 : r ^ 2 = 2 := by dsimp [r]; exact Real.sq_sqrt (by norm_num)
  have hfac : 1 - 6 * u + u ^ 2 = (u - (3 - 2 * r)) * (u - (3 + 2 * r)) := by
    dsimp [r]
    nlinarith [hs2]
  have hs : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * r := by
    dsimp [r]
    exact sqrt2m1_sq
  have hfirst : u - (3 - 2 * r) ≤ 0 := by linarith [hu1, hs]
  have hsp : 0 < r := by dsimp [r]; positivity
  have hsecond : u - (3 + 2 * r) ≤ 0 := by nlinarith [hu0, hsp]
  rw [hfac]
  exact mul_nonneg_of_nonpos_of_nonpos hfirst hsecond


/-- If `0 < Re w` and `|Im w| <= (sqrt 2 - 1) * Re w` then `Re(w^4) >= 0`. -/
theorem reFourth_nonneg_of_cone (w : ℂ) (hw0 : 0 < w.re)
    (habs : |w.im| ≤ (Real.sqrt 2 - 1) * w.re) : 0 ≤ (w ^ 4).re := by
  rw [re_fourth_poly]
  let a : ℝ := w.re
  let b : ℝ := w.im
  let c : ℝ := Real.sqrt 2 - 1
  have hc : 0 < c := by
    dsimp [c]
    have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [hsq, Real.sqrt_nonneg (2:ℝ)]
  have hca : 0 ≤ c * a := mul_nonneg (le_of_lt hc) (le_of_lt hw0)
  have habs' : |b| ≤ c * a := by simpa [a, b, c] using habs
  have hb2 : b ^ 2 ≤ (c * a) ^ 2 := by
    have h₁ : |b| ^ 2 ≤ (c * a) ^ 2 := pow_le_pow_left₀ (abs_nonneg b) habs' 2
    simpa [sq_abs] using h₁
  let u : ℝ := (b / a) ^ 2
  have hu0 : 0 ≤ u := by dsimp [u]; exact sq_nonneg (b / a)
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos hw0
  have ha_ne : a ≠ 0 := by simpa [a] using (ne_of_gt hw0)
  have hle_p : b ^ 2 ≤ c ^ 2 * a ^ 2 := by
    have hre : (c * a) ^ 2 = c ^ 2 * a ^ 2 := by ring
    nlinarith [hb2, hre]
  have hule : u ≤ c ^ 2 := by
    dsimp [u]
    rw [div_pow]
    exact (div_le_iff₀ ha2).mpr hle_p
  have hcone : 0 ≤ 1 - 6 * u + u ^ 2 := cone_nonneg u hu0 hule
  have hmain : a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 = a ^ 4 * (1 - 6 * u + u ^ 2) := by
    dsimp [u]
    field_simp [ha_ne]
  rw [hmain]
  have ha0 : 0 ≤ a := le_of_lt hw0
  have ha4 : 0 ≤ a ^ 4 := pow_nonneg ha0 4
  exact mul_nonneg ha4 hcone


end Finite3SignReduction
end Dev
end Source
end ConnesWeilRH


