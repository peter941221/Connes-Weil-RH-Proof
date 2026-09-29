/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1SpectralWeil
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Direct-product Laplace decay on a vertical strip (record 2265)

Record 2260 pinned the producer side of the weighted-zero C3' candidate to a
single missing Lean brick: a uniform quadratic-decay estimate for the
bilateral Laplace transform of the direct product `base ⋆ corr`, with the
constant obtained as the strip minimum of the two-channel product

`min (∫ e^{σx}‖b''‖ · ∫ e^{σx}‖c‖, ∫ e^{σx}‖c''‖ · ∫ e^{σx}‖b‖)`,

where `σ = Re s` runs over the centered strip that the spectral chain
evaluates at (`centeredXiCoordinate rho = (rho.re - 1/2) + i rho.im`,
`C1SpectralWeil.lean:275`).  This module lands that brick:

1. `sq_mul_exp_integral_eq` — the two-integration-by-parts identity
   `s ^ 2 * ∫ e^{sx} f = ∫ e^{sx} f''` for compactly supported `C²`
   functions, using Mathlib's whole-line integration-by-parts lemma
   `integral_mul_deriv_eq_deriv_mul_of_integrable` (no boundary terms since
   the products are compactly supported);
2. `norm_exp_integral_le_stripNorm` and `t_sq_mul_norm_exp_integral_le` —
   the two faces of the estimate: the trivial strip bound `‖∫ e^{sx} f‖ ≤
   ∫ e^{σx}‖f‖` and the second-derivative face `t ^ 2 * ‖∫ e^{sx} f‖ ≤
   ∫ e^{σx}‖f''‖`;
3. `laplaceAt_convolution_quadratic_bound` — the min-product bound for a
   `CompactLogTest` pair, via the source product law
   `laplaceAt_convolution`;
4. `laplaceAt_convolution_spectral_bound_of_strip` — the producer-shaped
   corollary: a strip hypothesis over `Set.Icc (-1/2) 1/2` on the two
   product channels yields the per-zero chain bound with constant
   `B / (2π)^2`, mirroring `exists_spectral_laplaceAt_quadratic_bound`.

The numeric content — that the committed 2197/2234/2243 envelope value
`B = 9506275.102584327` covers the centered strip — is a separate
artifact-level obligation (records 2264 and the pending certified
negative-half envelope); this module carries it as the explicit hypothesis
`hB` of the corollary.  No producer GO, no gate sign change, and no RH
claim is made here.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory Complex
open scoped ContDiff
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.C1SpectralWeil
open ConnesWeilRH.Source.CC20YoshidaNearZeros

/-- Strip-weighted `L¹` norm of a function on the vertical line `Re s = sigma`. -/
noncomputable def stripNorm (sigma : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp (sigma * x) * ‖f x‖

/-- Strip-weighted `L¹` norm of the second derivative of a function. -/
noncomputable def stripSecondNorm (sigma : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp (sigma * x) * ‖deriv (deriv f) x‖

theorem stripNorm_nonneg (sigma : ℝ) (f : ℝ → ℂ) : 0 ≤ stripNorm sigma f :=
  integral_nonneg fun x => mul_nonneg (Real.exp_nonneg (sigma * x)) (norm_nonneg (f x))

theorem stripSecondNorm_nonneg (sigma : ℝ) (f : ℝ → ℂ) :
    0 ≤ stripSecondNorm sigma f :=
  integral_nonneg fun x =>
    mul_nonneg (Real.exp_nonneg (sigma * x)) (norm_nonneg (deriv (deriv f) x))

/-- The Laplace evaluation unfolded into its raw integral. -/
theorem laplaceAt_eq_integral (f : CompactLogTest) (s : ℂ) :
    laplaceAt f s = ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f.test x := by
  unfold laplaceAt
  apply integral_congr_ae
  filter_upwards with x
  rw [exponentialWeight_apply]

/-- **Two integrations by parts against a complex exponential.**  For a
compactly supported `C²` function `f` with derivative chain `f'`, `f''`,
`s ^ 2 * ∫ e^{sx} f = ∫ e^{sx} f''`.  There are no boundary terms: with the
products compactly supported, Mathlib's whole-line integration by parts
applies twice. -/
theorem sq_mul_exp_integral_eq {f f' f'' : ℝ → ℂ} {s : ℂ}
    (h1 : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (h2 : ∀ x : ℝ, HasDerivAt f' (f'' x) x)
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hsupp : HasCompactSupport f) :
    s ^ 2 * (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f x)
      = ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f'' x := by
  set E : ℝ → ℂ := fun x => Complex.exp (s * (x : ℂ)) with hE
  set E' : ℝ → ℂ := fun x => E x * s with hE'
  have hEd : ∀ x : ℝ, HasDerivAt E (E' x) x := by
    intro x
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x :=
      Complex.ofRealCLM.hasDerivAt
    have hinner : HasDerivAt (fun t : ℝ => s * (t : ℂ)) s x := by
      simpa using hid.const_mul s
    simpa only [hE, hE'] using hinner.cexp
  have hcontE : Continuous E := by
    rw [hE]
    exact Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)
  have hsupp_f' : HasCompactSupport f' := by
    have hfe : f' = deriv f := funext fun x => (h1 x).deriv.symm
    rw [hfe]
    exact hsupp.deriv
  have hsupp_f'' : HasCompactSupport f'' := by
    have hfe : f'' = deriv f' := funext fun x => (h2 x).deriv.symm
    rw [hfe]
    exact hsupp_f'.deriv
  have hintfE : Integrable (fun x : ℝ => f x * E x) :=
    (hf.mul hcontE).integrable_of_hasCompactSupport hsupp.mul_right
  have hintf'E : Integrable (fun x : ℝ => f' x * E x) :=
    (hf'.mul hcontE).integrable_of_hasCompactSupport hsupp_f'.mul_right
  have hintf''E : Integrable (fun x : ℝ => f'' x * E x) :=
    (hf''.mul hcontE).integrable_of_hasCompactSupport hsupp_f''.mul_right
  have hintfE' : Integrable (fun x : ℝ => f x * E' x) := by
    have hEq : (fun x : ℝ => f x * E' x) = fun x : ℝ => s * (f x * E x) := by
      funext x
      rw [hE']
      ring
    rw [hEq]
    exact hintfE.const_mul s
  have hintf'E' : Integrable (fun x : ℝ => f' x * E' x) := by
    have hEq : (fun x : ℝ => f' x * E' x) = fun x : ℝ => s * (f' x * E x) := by
      funext x
      rw [hE']
      ring
    rw [hEq]
    exact hintf'E.const_mul s
  have hIBP1 : (∫ x : ℝ, f x * E' x) = -(∫ x : ℝ, f' x * E x) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => h1 x) (fun x _ => hEd x) hintfE' hintf'E hintfE
  have hIBP2 : (∫ x : ℝ, f' x * E' x) = -(∫ x : ℝ, f'' x * E x) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => h2 x) (fun x _ => hEd x) hintf'E' hintf''E hintf'E
  have hIBP1' : s * (∫ x : ℝ, f x * E x) = -(∫ x : ℝ, f' x * E x) := by
    have hpt : ∀ x : ℝ, f x * E' x = s * (f x * E x) := by
      intro x
      rw [hE']
      ring
    have hEq : (∫ x : ℝ, f x * E' x) = s * (∫ x : ℝ, f x * E x) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_const_mul s (fun x => f x * E x)]
    rw [← hEq, hIBP1]
  have hIBP2' : s * (∫ x : ℝ, f' x * E x) = -(∫ x : ℝ, f'' x * E x) := by
    have hpt : ∀ x : ℝ, f' x * E' x = s * (f' x * E x) := by
      intro x
      rw [hE']
      ring
    have hEq : (∫ x : ℝ, f' x * E' x) = s * (∫ x : ℝ, f' x * E x) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_const_mul s (fun x => f' x * E x)]
    rw [← hEq, hIBP2]
  have hcomb : s * s * (∫ x : ℝ, f x * E x) = (∫ x : ℝ, f'' x * E x) := by
    rw [mul_assoc, hIBP1', mul_neg, hIBP2', neg_neg]
  have hAE : (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f x)
      = (∫ x : ℝ, f x * E x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hE]
    ring
  have hBE : (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f'' x)
      = (∫ x : ℝ, f'' x * E x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hE]
    ring
  rw [hAE, hBE, pow_two]
  exact hcomb

/-- **Trivial strip bound.**  The Laplace integral at `s = σ + it` is at most
the strip-weighted `L¹` norm at `σ = Re s`. -/
theorem norm_exp_integral_le_stripNorm (sigma t : ℝ) (f : ℝ → ℂ) :
    ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x)‖
      ≤ stripNorm sigma f := by
  have hpt : ∀ x : ℝ,
      ‖Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x‖
        = Real.exp (sigma * x) * ‖f x‖ := by
    intro x
    rw [norm_mul, Complex.norm_exp]
    congr 1
    have hz : (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)).re
        = sigma * x := by
      have h2 : ((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)
          = ((sigma * x : ℝ) : ℂ) + ((t * x : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h2]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [hz]
  calc ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x)‖
      ≤ ∫ x : ℝ,
          ‖Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, Real.exp (sigma * x) * ‖f x‖ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = stripNorm sigma f := rfl

/-- **Second-derivative face.**  For a compactly supported `C²` function,
`t ^ 2 * ‖∫ e^{sx} f‖ ≤ ∫ e^{σx} ‖f''‖` with `s = σ + it`: the two-IBP
identity turns `t ^ 2` into a second derivative at the cost of the strip
weight. -/
theorem t_sq_mul_norm_exp_integral_le
    {f f' f'' : ℝ → ℂ} {sigma t : ℝ}
    (h1 : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (h2 : ∀ x : ℝ, HasDerivAt f' (f'' x) x)
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hsupp : HasCompactSupport f) :
    t ^ 2 * ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x)‖
      ≤ ∫ x : ℝ, Real.exp (sigma * x) * ‖f'' x‖ := by
  have hIBP := sq_mul_exp_integral_eq (s := (sigma : ℂ) + (t : ℂ) * Complex.I)
    h1 h2 hf hf' hf'' hsupp
  have hnormeq : ‖((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 *
      ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x)‖
      = ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f'' x)‖ := by
    have h := congrArg norm hIBP
    rwa [norm_mul, norm_pow] at h
  have hnormbound : ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f'' x)‖
      ≤ ∫ x : ℝ, Real.exp (sigma * x) * ‖f'' x‖ :=
    norm_exp_integral_le_stripNorm sigma t f''
  have hz : ‖((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 = sigma ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_add_mul_I sigma t
  have hts : t ^ 2 ≤ ‖((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hz]
    nlinarith [sq_nonneg sigma]
  calc t ^ 2 * ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x)‖
      ≤ ‖((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 *
          ‖(∫ x : ℝ,
            Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f x)‖ :=
        mul_le_mul_of_nonneg_right hts (norm_nonneg _)
    _ = ‖(∫ x : ℝ,
          Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f'' x)‖ :=
        hnormeq
    _ ≤ ∫ x : ℝ, Real.exp (sigma * x) * ‖f'' x‖ := hnormbound

/-- The second-derivative face for a compact log test, with the strip norm of
its literal second derivative. -/
theorem test_t_sq_mul_norm_le_stripSecond (f : CompactLogTest)
    (sigma t : ℝ) :
    t ^ 2 * ‖(∫ x : ℝ,
        Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * f.test x)‖
      ≤ stripSecondNorm sigma (f.test : ℝ → ℂ) := by
  have hdiff : Differentiable ℝ (f.test : ℝ → ℂ) :=
    (f.test.smooth ⊤).differentiable (by decide)
  have hderiv_diff : Differentiable ℝ (deriv (f.test : ℝ → ℂ)) :=
    ((f.test.smooth ⊤).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)).differentiable_deriv_two
  have hcont : Continuous (f.test : ℝ → ℂ) := (f.test.smooth ⊤).continuous
  have hderiv_cont : Continuous (deriv (f.test : ℝ → ℂ)) :=
    (f.test.smooth ⊤).continuous_deriv (by decide : (1 : ℕ∞ω) ≤ ∞)
  have hderiv2_cont : Continuous (deriv (deriv (f.test : ℝ → ℂ))) :=
    (ContDiff.deriv'
      ((f.test.smooth ⊤).of_le (by decide : (2 : ℕ∞ω) ≤ ∞))).continuous_deriv
      (by decide : (1 : ℕ∞ω) ≤ 1)
  have h := t_sq_mul_norm_exp_integral_le (sigma := sigma) (t := t)
    (f := (f.test : ℝ → ℂ)) (f' := deriv (f.test : ℝ → ℂ))
    (f'' := deriv (deriv (f.test : ℝ → ℂ)))
    (fun x => (hdiff.differentiableAt).hasDerivAt)
    (fun x => (hderiv_diff.differentiableAt).hasDerivAt)
    hcont hderiv_cont hderiv2_cont f.compactSupport
  simpa only [stripSecondNorm] using h

/-- **Direct-product decay with the min-product constant.**  For compact log
tests `b`, `c` and any `s = σ + it`,

`‖t / 2π‖ ^ 2 * ‖L (b ⋆ c) s‖ ≤ min (D₂ b · M c, D₂ c · M b) / (2π)^2`

where `M f = stripNorm σ f` and `D₂ f = stripSecondNorm σ f`.  The two
channels come from the trivial bound on one factor and the second-derivative
face on the other. -/
theorem laplaceAt_convolution_quadratic_bound
    (b c : CompactLogTest) (sigma t : ℝ) :
    ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖laplaceAt (b.convolution c) ((sigma : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ min (stripSecondNorm sigma (b.test : ℝ → ℂ) * stripNorm sigma (c.test : ℝ → ℂ))
            (stripSecondNorm sigma (c.test : ℝ → ℂ) * stripNorm sigma (b.test : ℝ → ℂ))
          / (2 * Real.pi) ^ 2 := by
  rw [laplaceAt_convolution]
  simp only [laplaceAt_eq_integral]
  rw [norm_mul]
  set Xb : ℝ := ‖(∫ x : ℝ,
    Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * b.test x)‖ with hXb
  set Xc : ℝ := ‖(∫ x : ℝ,
    Complex.exp (((sigma : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) * c.test x)‖ with hXc
  set Db : ℝ := stripSecondNorm sigma (b.test : ℝ → ℂ) with hDb
  set Dc : ℝ := stripSecondNorm sigma (c.test : ℝ → ℂ) with hDc
  set Mb : ℝ := stripNorm sigma (b.test : ℝ → ℂ) with hMb
  set Mc : ℝ := stripNorm sigma (c.test : ℝ → ℂ) with hMc
  have htb : t ^ 2 * Xb ≤ Db := by
    rw [hXb, hDb]
    exact test_t_sq_mul_norm_le_stripSecond b sigma t
  have htc : t ^ 2 * Xc ≤ Dc := by
    rw [hXc, hDc]
    exact test_t_sq_mul_norm_le_stripSecond c sigma t
  have hMb_le : Xb ≤ Mb := by
    rw [hXb, hMb]
    exact norm_exp_integral_le_stripNorm sigma t (b.test : ℝ → ℂ)
  have hMc_le : Xc ≤ Mc := by
    rw [hXc, hMc]
    exact norm_exp_integral_le_stripNorm sigma t (c.test : ℝ → ℂ)
  have hmin : t ^ 2 * (Xb * Xc) ≤ min (Db * Mc) (Dc * Mb) := by
    apply le_min
    · have h1 : t ^ 2 * (Xb * Xc) = (t ^ 2 * Xb) * Xc := by ring
      rw [h1]
      exact mul_le_mul htb hMc_le (norm_nonneg _)
        (stripSecondNorm_nonneg sigma (b.test : ℝ → ℂ))
    · have h1 : t ^ 2 * (Xb * Xc) = (t ^ 2 * Xc) * Xb := by ring
      rw [h1]
      exact mul_le_mul htc hMb_le (norm_nonneg _)
        (stripSecondNorm_nonneg sigma (c.test : ℝ → ℂ))
  have hL : ‖t / (2 * Real.pi)‖ ^ 2 * (Xb * Xc)
      = (t ^ 2 * (Xb * Xc)) / (2 * Real.pi) ^ 2 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      div_pow, sq_abs]
    ring
  calc ‖t / (2 * Real.pi)‖ ^ 2 * (Xb * Xc)
      = (t ^ 2 * (Xb * Xc)) / (2 * Real.pi) ^ 2 := hL
    _ ≤ min (Db * Mc) (Dc * Mb) / (2 * Real.pi) ^ 2 :=
        (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 2)).mpr hmin

/-- **Producer-shaped corollary.**  If the two product channels are bounded by
`B` on the centered strip `σ ∈ [-1/2, 1/2]` that the spectral chain evaluates
at, then every source nontrivial zero satisfies the chain-shaped bound

`‖Im ρ / 2π‖ ^ 2 * ‖L (b ⋆ c) (centeredXiCoordinate ρ)‖ ≤ B / (2π)^2`,

mirroring `exists_spectral_laplaceAt_quadratic_bound`.  The numeric
obligation — that the committed envelope value covers the centered strip —
enters only through `hB`. -/
theorem laplaceAt_convolution_spectral_bound_of_strip
    (b c : CompactLogTest) (B : ℝ)
    (hB : ∀ sigma ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      min (stripSecondNorm sigma (b.test : ℝ → ℂ) * stripNorm sigma (c.test : ℝ → ℂ))
          (stripSecondNorm sigma (c.test : ℝ → ℂ) * stripNorm sigma (b.test : ℝ → ℂ))
        ≤ B) :
    ∀ rho : sourceNontrivialZeroSet,
      ‖rho.1.im / (2 * Real.pi)‖ ^ 2 *
          ‖laplaceAt (b.convolution c) (centeredXiCoordinate rho)‖
        ≤ B / (2 * Real.pi) ^ 2 := by
  intro rho
  have hre_lo : -(1 / 2 : ℝ) ≤ rho.1.re - 1 / 2 := by
    have := sourceNontrivialZero_zero_lt_re rho.2
    linarith
  have hre_hi : rho.1.re - 1 / 2 ≤ 1 / 2 := by
    have := sourceNontrivialZero_re_lt_one rho.2
    linarith
  have hbound := laplaceAt_convolution_quadratic_bound b c (rho.1.re - 1 / 2) rho.1.im
  have harg : centeredXiCoordinate rho =
      (((rho.1.re - 1 / 2 : ℝ) : ℂ) + (rho.1.im : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [centeredXiCoordinate]
  rw [harg]
  exact le_trans hbound
    ((div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 2)).mpr
      (hB _ ⟨hre_lo, hre_hi⟩))

end Dev
end ConnesWeilRH
