import ConnesWeilRH.Dev.C1RouteBThetaTrigCoarse2981
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

noncomputable def routeBThetaTCoarse2982 (θ : ℝ) : ℂ :=
  (1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ)

noncomputable def routeBThetaTCoarseRect2982 : ComplexRect2427 :=
  ComplexRect2427.mk ((24 : ℝ) / 1000) ((28 : ℝ) / 1000)
    (-(44 : ℝ) / 1000) (-(42 : ℝ) / 1000)

theorem routeBThetaTCoarseMem2982 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ComplexRect2427.Mem
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ))
      routeBThetaTCoarseRect2982 := by
  have ht := routeBThetaTrigCoarse2981 hδlo hδhi
  change routeBThetaTCoarseRect2982.reLo ≤
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).re ∧
    (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).re ≤
      routeBThetaTCoarseRect2982.reHi ∧
    routeBThetaTCoarseRect2982.imLo ≤
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).im ∧
      (routeBThetaTCoarse2982 (5 * Real.pi / 3 + δ)).im ≤
      routeBThetaTCoarseRect2982.imHi
  simp only [routeBThetaTCoarseRect2982, ComplexRect2427.mk,
    routeBThetaTCoarse2982, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring_nf
  have harg : Real.pi * (5 / 3 : ℝ) + δ = 5 * Real.pi / 3 + δ := by ring
  rw [harg] at *
  rcases ht with ⟨hsl, hsu, hcl, hcu⟩
  constructor
  · have h := mul_le_mul_of_nonneg_right hcl.le (by norm_num : (0 : ℝ) ≤ 1 / 20)
    norm_num at h ⊢
    nlinarith [h]
  constructor
  · have h := mul_le_mul_of_nonneg_right hcu.le (by norm_num : (0 : ℝ) ≤ 1 / 20)
    norm_num at h ⊢
    nlinarith [h]
  constructor
  · have h := mul_lt_mul_of_pos_right hsl (by norm_num : (0 : ℝ) < 1 / 20)
    norm_num at h ⊢
    nlinarith [h]
  · have h := mul_lt_mul_of_pos_right hsu (by norm_num : (0 : ℝ) < 1 / 20)
    norm_num at h ⊢
    nlinarith [h]

end ConnesWeilRH.Dev
