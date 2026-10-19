import ConnesWeilRH.Dev.C1RouteBThetaTrigSharper2994
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

noncomputable def routeBThetaTSharperRect2995 : ComplexRect2427 :=
  ComplexRect2427.mk ((24 : ℝ) / 1000) ((275 : ℝ) / 10000)
    (-(435 : ℝ) / 10000) (-(42 : ℝ) / 1000)

noncomputable def routeBThetaTSharper2995 (θ : ℝ) : ℂ :=
  (1 / 20 : ℝ) * (Real.cos θ + Complex.I * Real.sin θ)

theorem routeBThetaTSharperMem2995 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ComplexRect2427.Mem
      (routeBThetaTSharper2995 (5 * Real.pi / 3 + δ))
      routeBThetaTSharperRect2995 := by
  have ht := routeBThetaTrigSharper2994 hδlo hδhi
  change routeBThetaTSharperRect2995.reLo ≤
      (routeBThetaTSharper2995 (5 * Real.pi / 3 + δ)).re ∧
    (routeBThetaTSharper2995 (5 * Real.pi / 3 + δ)).re ≤
      routeBThetaTSharperRect2995.reHi ∧
    routeBThetaTSharperRect2995.imLo ≤
      (routeBThetaTSharper2995 (5 * Real.pi / 3 + δ)).im ∧
    (routeBThetaTSharper2995 (5 * Real.pi / 3 + δ)).im ≤
      routeBThetaTSharperRect2995.imHi
  simp only [routeBThetaTSharperRect2995, ComplexRect2427.mk,
    routeBThetaTSharper2995, Complex.mul_re, Complex.mul_im, Complex.add_re,
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
