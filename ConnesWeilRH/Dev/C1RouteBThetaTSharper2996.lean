import ConnesWeilRH.Dev.C1RouteBThetaTrigSharper2994
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

noncomputable def routeBThetaTSharperRect2996 : ComplexRect2427 :=
  ComplexRect2427.mk ((255 : ℝ) / 10000) ((26 : ℝ) / 1000)
    (-(43 : ℝ) / 1000) (-(425 : ℝ) / 10000)

noncomputable def routeBThetaTSharper2996 (θ : ℝ) : ℂ :=
  (1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ)

theorem routeBThetaTSharperMem2996 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ComplexRect2427.Mem
      (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ))
      routeBThetaTSharperRect2996 := by
  have ht := routeBThetaTrigSharper2994 hδlo hδhi
  change routeBThetaTSharperRect2996.reLo ≤
      (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).re ∧
    (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).re ≤
      routeBThetaTSharperRect2996.reHi ∧
    routeBThetaTSharperRect2996.imLo ≤
      (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).im ∧
    (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).im ≤
      routeBThetaTSharperRect2996.imHi
  simp only [routeBThetaTSharperRect2996, ComplexRect2427.mk,
    routeBThetaTSharper2996, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring_nf
  have harg : Real.pi * (5 / 3 : ℝ) + δ = 5 * Real.pi / 3 + δ := by ring
  rw [harg] at *
  rcases ht with ⟨hsl, hsu, hcl, hcu⟩
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

end ConnesWeilRH.Dev
