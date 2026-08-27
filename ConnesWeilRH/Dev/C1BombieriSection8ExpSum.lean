/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerFull

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, tenth slice: the finite-window exponential integral

First brick of the (8.11) transport (Bombieri's Lemma 10, book
pp.209-212): the finite-window integral of the pure exponential that
the Gram identity's sinc term integrates to,

```
∫_{−t}^{t} e^{iθu} du = 2 sin(θt)/θ   (θ ≠ 0),      ∫ = 2t   (θ = 0).
```

Route (real channel — no complex division anywhere): `exp_mul_I`
splits the integrand pointwise into `↑(cos θu) + I·↑(sin θu)`; the
cosine part integrates by the real fundamental theorem with
`sin(θu)/θ` as the antiderivative (the `θ` is divided INSIDE, so no
integral-linearity node-mismatch is ever exercised), and the sine
part is odd, so it vanishes on the symmetric window through a
real-valued mirror of the landed halving identity.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8ExpSum

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open MeasureTheory

/-- Real-valued mirror of the parity-split halving identity: the
symmetric-window integral is the half-line integral of the reflected
sum. -/
theorem integral_symmetry_half_real (t : Real) (ht : 0 ≤ t) (f : Real → Real)
    (hfc : Continuous f) :
    ∫ x in -t..t, f x = ∫ x in 0..t, (f x + f (-x)) := by
  have hA : IntervalIntegrable f volume (-t) 0 := Continuous.intervalIntegrable hfc (-t) 0
  have hB : IntervalIntegrable f volume 0 t := Continuous.intervalIntegrable hfc 0 t
  have hB' : IntervalIntegrable (fun x : Real => f (-x)) volume 0 t :=
    Continuous.intervalIntegrable (hfc.comp continuous_neg) 0 t
  rw [intervalIntegral.integral_add hB hB',
    intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := t),
    neg_zero,
    ← intervalIntegral.integral_add_adjacent_intervals hA hB]
  ring

/-- d/dx sin(θx) = θ·cos(θx), same-type chain rule through the inner
multiplication. -/
theorem hasDerivAt_sin_mul_real (θ u : Real) :
    HasDerivAt (fun x : Real => Real.sin (θ * x)) (θ * Real.cos (θ * u)) u := by
  have hinner : HasDerivAt (fun x : Real => θ * x) (θ * 1) u :=
    (hasDerivAt_id u).const_mul θ
  rw [mul_one] at hinner
  have h : HasDerivAt (fun x : Real => Real.sin (θ * x)) (Real.cos (θ * u) * θ) u :=
    (Real.hasDerivAt_sin (θ * u)).comp u hinner
  exact h.congr_deriv (by ring)

/-- d/dx cos(θx) = −θ·sin(θx). -/
theorem hasDerivAt_cos_mul_real (θ u : Real) :
    HasDerivAt (fun x : Real => Real.cos (θ * x)) (-(θ * Real.sin (θ * u))) u := by
  have hinner : HasDerivAt (fun x : Real => θ * x) (θ * 1) u :=
    (hasDerivAt_id u).const_mul θ
  rw [mul_one] at hinner
  have h : HasDerivAt (fun x : Real => Real.cos (θ * x)) (-(Real.sin (θ * u)) * θ) u :=
    (Real.hasDerivAt_cos (θ * u)).comp u hinner
  exact h.congr_deriv (by ring)

/-- The pointwise Euler split, stated with the `I` factor on the LEFT
(matching `integral_const_mul`'s multiplication form). -/
theorem exp_i_mul_real (θ x : Real) :
    Complex.exp ((θ * x : Real) * Complex.I)
      = Complex.ofReal (Real.cos (θ * x))
        + Complex.I * Complex.ofReal (Real.sin (θ * x)) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- The cosine half: `∫_{−t}^{t} cos(θx) = 2 sin(θt)/θ` for `θ ≠ 0`
(real fundamental theorem with `sin(θx)/θ` as antiderivative). -/
theorem integral_cos_mul_real (t θ : Real) (ht : 0 ≤ t) (hθ : θ ≠ 0) :
    ∫ x in -t..t, Real.cos (θ * x) = 2 * Real.sin (θ * t) / θ := by
  have hcoscont : Continuous fun x : Real => Real.cos (θ * x) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cos_mul_real θ x).continuousAt
  have hderiv : ∀ x : Real, HasDerivAt (fun y : Real => Real.sin (θ * y) / θ)
      (Real.cos (θ * x)) x := fun x =>
    ((hasDerivAt_sin_mul_real θ x).div_const θ).congr_deriv (by field_simp)
  have hint : IntervalIntegrable (fun x : Real => Real.cos (θ * x)) volume (-t) t :=
    Continuous.intervalIntegrable hcoscont (-t) t
  have hFTA := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint
  rw [mul_neg, Real.sin_neg] at hFTA
  rw [hFTA]
  ring

/-- The sine half vanishes on the symmetric window: `sin` is odd, and
the halving identity reduces the symmetric integral to the integral
of the zero function. -/
theorem integral_sin_mul_real (t θ : Real) (ht : 0 ≤ t) :
    ∫ x in -t..t, Real.sin (θ * x) = 0 := by
  have hcont : Continuous fun x : Real => Real.sin (θ * x) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sin_mul_real θ x).continuousAt
  rw [integral_symmetry_half_real t ht (fun x : Real => Real.sin (θ * x)) hcont]
  have hpt : (fun x : Real =>
        (fun y : Real => Real.sin (θ * y)) x + (fun y : Real => Real.sin (θ * y)) (-x))
      = fun _ : Real => (0 : Real) := by
    funext x
    simp only []
    rw [mul_neg, Real.sin_neg]
    ring
  rw [hpt, intervalIntegral.integral_const (0 : Real), smul_eq_mul]
  ring

/-- FLAGSHIP (slice 10): the finite-window exponential integral —
`∫_{−t}^{t} e^{iθu} du = 2 sin(θt)/θ` for `θ ≠ 0`.  This is the
integral readback of the sinc term `2 sin(t(γ−γ'))/(γ−γ')` in the
Lemma-10 Gram identity, the engine of the (8.10)→(8.11) step. -/
theorem integral_exp_i_window (t θ : Real) (ht : 0 ≤ t) (hθ : θ ≠ 0) :
    ∫ x in -t..t, Complex.exp ((θ * x : Real) * Complex.I)
      = Complex.ofReal (2 * Real.sin (θ * t) / θ) := by
  have hsplit : (fun x : Real => Complex.exp ((θ * x : Real) * Complex.I))
      = fun x : Real => Complex.ofReal (Real.cos (θ * x))
          + Complex.I * Complex.ofReal (Real.sin (θ * x)) := by
    funext x
    exact exp_i_mul_real θ x
  have hcoscont : Continuous fun x : Real => Complex.ofReal (Real.cos (θ * x)) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cos_mul_real θ x).continuousAt)
  have hsincont : Continuous fun x : Real => Complex.ofReal (Real.sin (θ * x)) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_sin_mul_real θ x).continuousAt)
  have hIc : IntervalIntegrable
      (fun x : Real => Complex.ofReal (Real.cos (θ * x))) volume (-t) t :=
    Continuous.intervalIntegrable hcoscont (-t) t
  have hIs2 : IntervalIntegrable
      (fun x : Real => Complex.I * Complex.ofReal (Real.sin (θ * x))) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hsincont) (-t) t
  rw [hsplit, intervalIntegral.integral_add hIc hIs2,
    intervalIntegral.integral_ofReal, integral_cos_mul_real t θ ht hθ,
    intervalIntegral.integral_const_mul (Complex.I),
    intervalIntegral.integral_ofReal, integral_sin_mul_real t θ ht,
    Complex.ofReal_zero, mul_zero, add_zero]

/-- The diagonal: the `θ = 0` integrand is the constant `1`, so the
window integral is `2t`. -/
theorem integral_exp_i_window_zero (t : Real) (ht : 0 ≤ t) :
    ∫ x in -t..t, Complex.exp (((0 : Real) * x) * Complex.I) = (2 * t : ℂ) := by
  have hf : (fun x : Real => Complex.exp (((0 : Real) * x) * Complex.I))
      = fun _ : Real => (1 : ℂ) := by
    funext x
    simp
  rw [hf, intervalIntegral.integral_const ((1 : ℂ)), Complex.real_smul]
  push_cast
  ring

end C1BombieriSection8ExpSum
end Source
end ConnesWeilRH
