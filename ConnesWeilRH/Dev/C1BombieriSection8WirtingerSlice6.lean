/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice4

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), sixth slice: the odd envelope core

The mirror of slices 1-2 for the ODD envelope `φ₋(u) = e^{u/2} − e^{−u/2}`
of Bombieri's Lemma 10 (book pp.209-212):

* `phiOdd` with its derivative `φ₋' = ½(e^{u/2} + e^{−u/2})` and the ODE
  `φ₋'' = ¼φ₋`;
* the square expansions `φ₋² = e^u − 2 + e^{−u}` and
  `φ₋'² = ¼(e^u + 2 + e^{−u})`;
* the envelope quadratic integral `¼∫φ₋² + ∫φ₋'² = e^t − e^{−t}` — the
  SAME constant `R` as the even case (the `±2` terms cancel);
* the IBP core identity and its vanishing at zero endpoints.

The Q-form integrand itself is parity-independent, so the real channel
of slice 4 is reused verbatim; only the IBP weights are mirrored here.
DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerSlice6

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open MeasureTheory

/-- The odd envelope `φ₋(u) = e^{u/2} − e^{−u/2}`. -/
noncomputable def phiOdd (u : Real) : Real := Real.exp (u / 2) - Real.exp (-u / 2)

/-- The odd envelope derivative `φ₋'(u) = ½(e^{u/2} + e^{−u/2})`. -/
noncomputable def phiOddDeriv (u : Real) : Real :=
  (1 / 2 : Real) * (Real.exp (u / 2) + Real.exp (-u / 2))

/-- The real exponential integral over any interval (fundamental theorem). -/
private theorem integral_exp_real (a b : Real) :
    ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => Real.hasDerivAt_exp x)
    (Continuous.intervalIntegrable Real.continuous_exp a b)

/-- The reflected exponential integral. -/
private theorem integral_expNeg_real (a b : Real) :
    ∫ x in a..b, Real.exp (-x) = Real.exp (-a) - Real.exp (-b) := by
  have h := intervalIntegral.integral_comp_neg (f := Real.exp) (a := a) (b := b)
  rw [h]
  exact integral_exp_real (-b) (-a)

private theorem expHalf_mul_expHalf (u : Real) :
    Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
  rw [← Real.exp_add (u / 2) (u / 2), show (u / 2 + u / 2 : Real) = u from by ring]

private theorem expHalf_mul_expNegHalf (u : Real) :
    Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
  rw [← Real.exp_add (u / 2) (-u / 2),
    show (u / 2 + -u / 2 : Real) = 0 from by ring, Real.exp_zero]

private theorem expNegHalf_mul_expNegHalf (u : Real) :
    Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
  rw [← Real.exp_add (-u / 2) (-u / 2),
    show (-u / 2 + -u / 2 : Real) = -u from by ring]

theorem hasDerivAt_phiOdd (u : Real) :
    HasDerivAt phiOdd ((1 / 2 : Real) * (Real.exp (u / 2) + Real.exp (-u / 2))) u :=
  (hasDerivAt_expHalf u).sub (hasDerivAt_expNegHalf u) |>.congr_deriv (by ring)

theorem phiOdd_ode (u : Real) :
    HasDerivAt (fun y : Real => (1 / 2 : Real) * (Real.exp (y / 2) + Real.exp (-y / 2)))
      ((1 / 4 : Real) * phiOdd u) u := by
  have hrw : (fun y : Real => (1 / 2 : Real) * (Real.exp (y / 2) + Real.exp (-y / 2)))
      = fun y : Real => (1 / 2 : Real) * Real.exp (y / 2)
          + (1 / 2 : Real) * Real.exp (-y / 2) := by
    funext y
    ring
  rw [hrw]
  refine HasDerivAt.add
    (HasDerivAt.const_mul (1 / 2 : Real) (hasDerivAt_expHalf u))
    (HasDerivAt.const_mul (1 / 2 : Real) (hasDerivAt_expNegHalf u)) |>.congr_deriv ?_
  unfold phiOdd
  ring

/-- The pointwise square of the odd envelope. -/
theorem phiOdd_sq (u : Real) :
    phiOdd u * phiOdd u = Real.exp u - 2 + Real.exp (-u) := by
  unfold phiOdd
  rw [show (Real.exp (u / 2) - Real.exp (-u / 2))
        * (Real.exp (u / 2) - Real.exp (-u / 2))
      = Real.exp (u / 2) * Real.exp (u / 2)
        - 2 * (Real.exp (u / 2) * Real.exp (-u / 2))
        + Real.exp (-u / 2) * Real.exp (-u / 2) from by ring,
    expHalf_mul_expHalf, expHalf_mul_expNegHalf, expNegHalf_mul_expNegHalf]
  ring

/-- The pointwise square of the odd envelope derivative. -/
theorem phiOddDeriv_sq (u : Real) :
    phiOddDeriv u * phiOddDeriv u
      = (1 / 4 : Real) * (Real.exp u + 2 + Real.exp (-u)) := by
  unfold phiOddDeriv
  rw [show ((1 / 2 : Real) * (Real.exp (u / 2) + Real.exp (-u / 2)))
        * ((1 / 2 : Real) * (Real.exp (u / 2) + Real.exp (-u / 2)))
      = (1 / 4 : Real) * (Real.exp (u / 2) * Real.exp (u / 2)
          + 2 * (Real.exp (u / 2) * Real.exp (-u / 2))
          + Real.exp (-u / 2) * Real.exp (-u / 2)) from by ring,
    expHalf_mul_expHalf, expHalf_mul_expNegHalf, expNegHalf_mul_expNegHalf]
  ring

theorem hasDerivAt_g_mul_phiOdd' (g gp : Real → Complex) (x : Real)
    (hg : HasDerivAt g (gp x) x) :
    HasDerivAt (fun y : Real =>
        g y * Complex.ofReal ((1 / 2 : Real) * (Real.exp (y / 2) + Real.exp (-y / 2))))
      (gp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2)))
        + g x * Complex.ofReal ((1 / 4 : Real) * phiOdd x)) x := by
  refine HasDerivAt.mul hg (hasDerivAt_cast (phiOdd_ode x)) |>.congr_deriv ?_
  ring

/-- The IBP core identity for the odd envelope. -/
theorem ibpCoreOdd (t : Real) (g gp : Real → Complex)
    (hg : ∀ x, HasDerivAt g (gp x) x) (hgc : Continuous gp) :
    ∫ x in -t..t,
        (gp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2)))
          + g x * Complex.ofReal ((1 / 4 : Real) * phiOdd x))
      = g t * Complex.ofReal ((1 / 2 : Real) * (Real.exp (t / 2) + Real.exp (-t / 2)))
        - g (-t) * Complex.ofReal
            ((1 / 2 : Real) * (Real.exp (-t / 2) + Real.exp (t / 2))) := by
  have hR1 : Continuous fun x : Real => Real.exp (x / 2) :=
    Real.continuous_exp.comp (continuous_id.div_const (2 : Real))
  have hR2 : Continuous fun x : Real => Real.exp (-x / 2) := by
    have hrw : (fun x : Real => Real.exp (-x / 2))
        = fun x : Real => Real.exp (x / (-2 : Real)) := by
      funext x
      congr 1
      simp [neg_div, div_neg]
    rw [hrw]
    exact Real.continuous_exp.comp (continuous_id.div_const (-2 : Real))
  have hgcE : Continuous fun x : Real =>
      Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2))) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (hR1.add hR2))
  have hphiEc : Continuous fun x : Real => Complex.ofReal ((1 / 4 : Real) * phiOdd x) := by
    unfold phiOdd
    exact Complex.continuous_ofReal.comp (continuous_const.mul (hR1.sub hR2))
  have hgCont : Continuous g := continuous_iff_continuousAt.mpr
    fun x => (hg x).continuousAt
  have hcont : Continuous fun x : Real =>
      gp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2)))
        + g x * Complex.ofReal ((1 / 4 : Real) * phiOdd x) :=
    (hgc.mul hgcE).add (hgCont.mul hphiEc)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_g_mul_phiOdd' g gp x (hg x))
    (Continuous.intervalIntegrable hcont (-t) t)
  rw [neg_neg] at hmain
  exact hmain

/-- The IBP core vanishes on functions with zero endpoints. -/
theorem ibpCoreOdd_zero (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    ∫ x in -t..t,
        (Fp x * Complex.ofReal
            ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2)))
          + F x * Complex.ofReal ((1 / 4 : Real) * phiOdd x))
      = 0 := by
  have h := ibpCoreOdd t F Fp hF hFc
  rw [h1, h2] at h
  simpa using h

/-- The odd envelope quadratic integral: `¼∫φ₋² + ∫φ₋'² = e^t − e^{−t}`
— the SAME constant `R` as the even case (the `±2` terms cancel). -/
theorem envelopeIntegralOdd (t : Real) :
    (1 / 4 : Real) * (∫ x in -t..t, phiOdd x * phiOdd x)
      + (∫ x in -t..t, phiOddDeriv x * phiOddDeriv x)
      = Real.exp t - Real.exp (-t) := by
  have hf : (fun x : Real => phiOdd x * phiOdd x)
      = fun x : Real => Real.exp x - 2 + Real.exp (-x) := by
    funext x
    exact phiOdd_sq x
  have hg : (fun x : Real => phiOddDeriv x * phiOddDeriv x)
      = fun x : Real => (1 / 4 : Real) * (Real.exp x + 2 + Real.exp (-x)) := by
    funext x
    exact phiOddDeriv_sq x
  have hA : IntervalIntegrable (fun x : Real => Real.exp x) volume (-t) t :=
    Continuous.intervalIntegrable Real.continuous_exp (-t) t
  have hN : IntervalIntegrable (fun x : Real => Real.exp (-x)) volume (-t) t :=
    Continuous.intervalIntegrable (Real.continuous_exp.comp continuous_neg) (-t) t
  have hC : IntervalIntegrable (fun _ : Real => (2 : Real)) volume (-t) t :=
    Continuous.intervalIntegrable continuous_const (-t) t
  have hSub2 : IntervalIntegrable (fun x : Real => Real.exp x - 2) volume (-t) t :=
    hA.sub hC
  have hAdd2 : IntervalIntegrable (fun x : Real => Real.exp x + 2) volume (-t) t :=
    hA.add hC
  rw [hf, hg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hSub2 hN,
    intervalIntegral.integral_sub hA hC,
    intervalIntegral.integral_const (2 : Real),
    intervalIntegral.integral_add hAdd2 hN,
    intervalIntegral.integral_add hA hC,
    intervalIntegral.integral_const (2 : Real),
    integral_exp_real, integral_expNeg_real]
  simp only [smul_eq_mul]
  ring

end C1BombieriSection8WirtingerSlice6
end Source
end ConnesWeilRH
