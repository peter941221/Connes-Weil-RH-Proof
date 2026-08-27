/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice6

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), seventh slice: the odd-case inequality

The odd mirror of slices 3 and 5: with the odd envelope `φ₋` of slice 6
the Q-shift identity holds verbatim,

```
Q(F + c·φ₋) = Q(F) + c·conj(c)·(e^t − e^{−t}),
```

(the Q-form integrand is parity-independent; only the IBP weights are
mirrored), and the flagship `wirtingerOdd` gives the odd case of the
Wirtinger-type inequality (8.13) for a C¹ ODD function `Z` with `t > 0`:

```
Q(Z) = ↑( normSq(Z(t)) · (e^t − e^{−t}) / φ₋(t)² + S ),   S ≥ 0,
```

Since `(e^t − e^{−t}) / (e^{t/2} − e^{−t/2})² = cosh(t/2)/sinh(t/2)`
(= the `coth(t/2)` of the book's (8.13); Mathlib has no `coth`, so the
weight is stated through `cosh`/`sinh`), this is `Q(Z) ≥ coth(t/2)·|Z(t)|²`
in the real-channel shape forced by the orderless `ℂ`.
DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerSlice7

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice4
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice6
open MeasureTheory

/-- The odd IBP-core integrand: exactly the integrand of `ibpCoreOdd`. -/
private noncomputable def xIntegrandOdd (f fp : Real → Complex) (x : Real) : Complex :=
  fp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2)))
    + f x * Complex.ofReal ((1 / 4 : Real) * phiOdd x)

/-- The odd R-form integrand (the odd envelope quadratic density). -/
private noncomputable def rIntegrandCOdd (x : Real) : Complex :=
  Complex.ofReal ((1 / 4 : Real)) * (Complex.ofReal (phiOdd x) * Complex.ofReal (phiOdd x))
    + Complex.ofReal (phiOddDeriv x) * Complex.ofReal (phiOddDeriv x)

/-- `Xint(conj F) = conj(Xint(F))` pointwise for the odd weights. -/
theorem xIntegrandOdd_conj (F Fp : Real → Complex) (x : Real) :
    xIntegrandOdd (fun y => (starRingEnd ℂ) (F y)) (fun y => (starRingEnd ℂ) (Fp y)) x
      = (starRingEnd ℂ) (xIntegrandOdd F Fp x) := by
  unfold xIntegrandOdd
  rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    star_ofReal, star_ofReal]

/-- The odd IBP-core integral vanishes at zero endpoints (readback through
the `xIntegrandOdd` definitional form). -/
theorem xIntegralOdd_zero (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    ∫ x in -t..t, xIntegrandOdd F Fp x = 0 :=
  ibpCoreOdd_zero t F Fp hF hFc h1 h2

/-- The conjugated odd IBP-core integral also vanishes: no `HasDerivAt`
through `conj` is needed, only the integral-level transport. -/
theorem xIntegralOdd_conj_zero (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    ∫ x in -t..t, xIntegrandOdd (fun y => (starRingEnd ℂ) (F y))
        (fun y => (starRingEnd ℂ) (Fp y)) x = 0 := by
  have hpt : (fun x : Real => xIntegrandOdd (fun y => (starRingEnd ℂ) (F y))
      (fun y => (starRingEnd ℂ) (Fp y)) x)
      = fun x : Real => (starRingEnd ℂ) (xIntegrandOdd F Fp x) := by
    funext x
    exact xIntegrandOdd_conj F Fp x
  rw [hpt, integral_star_interval, xIntegralOdd_zero t F Fp hF hFc h1 h2, map_zero]

/-- The odd R-integral through the real channel: `∫ rIntegrandCOdd
= e^t − e^{−t}` (the SAME constant as the even case). -/
theorem rIntegralOdd (t : Real) :
    ∫ x in -t..t, rIntegrandCOdd x = Complex.ofReal (Real.exp t - Real.exp (-t)) := by
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
  have hphi : Continuous fun x : Real => phiOdd x := by
    unfold phiOdd
    exact hR1.sub hR2
  have hphid : Continuous fun x : Real => phiOddDeriv x := by
    unfold phiOddDeriv
    exact continuous_const.mul (hR1.add hR2)
  have hA : IntervalIntegrable (fun x : Real => (1 / 4 : Real) * (phiOdd x * phiOdd x))
      volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul (hphi.mul hphi)) (-t) t
  have hB : IntervalIntegrable (fun x : Real => phiOddDeriv x * phiOddDeriv x)
      volume (-t) t := Continuous.intervalIntegrable (hphid.mul hphid) (-t) t
  have hfun : (fun x : Real => rIntegrandCOdd x)
      = fun x : Real => Complex.ofReal ((1 / 4 : Real) * (phiOdd x * phiOdd x)
          + phiOddDeriv x * phiOddDeriv x) := by
    funext x
    unfold rIntegrandCOdd
    rw [← Complex.ofReal_mul (phiOdd x) (phiOdd x),
      ← Complex.ofReal_mul ((1 : Real) / 4) (phiOdd x * phiOdd x),
      ← Complex.ofReal_mul (phiOddDeriv x) (phiOddDeriv x), ← Complex.ofReal_add]
  rw [hfun, intervalIntegral.integral_ofReal, intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_const_mul, envelopeIntegralOdd]

/-- The pointwise Q-shift expansion for the odd envelope. -/
theorem qIntegrandOdd_expansion (F Fp : Real → Complex) (c : Complex) (x : Real) :
    qIntegrand (fun y => F y + c * Complex.ofReal (phiOdd y))
        (fun y => Fp y + c * Complex.ofReal (phiOddDeriv y)) x
      = qIntegrand F Fp x
        + (starRingEnd ℂ) c * xIntegrandOdd F Fp x
        + c * xIntegrandOdd (fun y => (starRingEnd ℂ) (F y))
            (fun y => (starRingEnd ℂ) (Fp y)) x
        + c * (starRingEnd ℂ) c * rIntegrandCOdd x := by
  unfold qIntegrand xIntegrandOdd rIntegrandCOdd phiOddDeriv
  rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    star_ofReal, star_ofReal,
    Complex.ofReal_mul ((1 : Real) / 4) (phiOdd x)]
  ring

/-- FLAGSHIP (slice 7): the odd Q-shift identity.  With `F(±t) = 0` the
two odd IBP-core cross integrals vanish, so the quadratic form of
`F + c·φ₋` is that of `F` plus `c·conj(c)·(e^t − e^{−t})` — the SAME
constant `R = 2 sinh t` as the even case. -/
theorem qShiftOdd (t : Real) (F Fp : Real → Complex) (c : Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    (∫ x in -t..t, qIntegrand (fun y => F y + c * Complex.ofReal (phiOdd y))
        (fun y => Fp y + c * Complex.ofReal (phiOddDeriv y)) x)
      = (∫ x in -t..t, qIntegrand F Fp x)
        + c * (starRingEnd ℂ) c * Complex.ofReal (Real.exp t - Real.exp (-t)) := by
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    fun x => (hF x).continuousAt
  have hstar : ∀ u : Real → Complex, Continuous u →
      Continuous fun x : Real => (starRingEnd ℂ) (u x) := by
    intro u hu
    exact continuous_star.comp hu
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
  have hphi : Continuous fun x : Real => phiOdd x := by
    unfold phiOdd
    exact hR1.sub hR2
  have hphid : Continuous fun x : Real => phiOddDeriv x := by
    unfold phiOddDeriv
    exact continuous_const.mul (hR1.add hR2)
  have hphiEc : Continuous fun x : Real =>
      Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) + Real.exp (-x / 2))) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (hR1.add hR2))
  have hphiEc0 : Continuous fun x : Real => Complex.ofReal (phiOdd x) :=
    Complex.continuous_ofReal.comp hphi
  have hphiEc2 : Continuous fun x : Real =>
      Complex.ofReal ((1 / 4 : Real) * phiOdd x) :=
    Complex.continuous_ofReal.comp (continuous_const.mul hphi)
  have hIc : Continuous fun x : Real => xIntegrandOdd F Fp x := by
    unfold xIntegrandOdd
    exact (hFc.mul hphiEc).add (hFcont.mul hphiEc2)
  have hAc : Continuous fun x : Real => qIntegrand F Fp x := by
    unfold qIntegrand
    exact (continuous_const.mul (hFcont.mul (hstar _ hFcont))).add
      (hFc.mul (hstar _ hFc))
  have hCc : Continuous fun x : Real =>
      xIntegrandOdd (fun y => (starRingEnd ℂ) (F y)) (fun y => (starRingEnd ℂ) (Fp y)) x := by
    unfold xIntegrandOdd
    exact ((hstar _ hFc).mul hphiEc).add ((hstar _ hFcont).mul hphiEc2)
  have hDc : Continuous fun x : Real => rIntegrandCOdd x := by
    unfold rIntegrandCOdd phiOddDeriv
    exact (continuous_const.mul (hphiEc0.mul hphiEc0)).add (hphiEc.mul hphiEc)
  have hiA : IntervalIntegrable (fun x : Real => qIntegrand F Fp x) volume (-t) t :=
    Continuous.intervalIntegrable hAc (-t) t
  have hiB : IntervalIntegrable
      (fun x : Real => (starRingEnd ℂ) c * xIntegrandOdd F Fp x) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hIc) (-t) t
  have hiC : IntervalIntegrable
      (fun x : Real => c * xIntegrandOdd (fun y => (starRingEnd ℂ) (F y))
        (fun y => (starRingEnd ℂ) (Fp y)) x) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hCc) (-t) t
  have hiD : IntervalIntegrable
      (fun x : Real => c * (starRingEnd ℂ) c * rIntegrandCOdd x) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hDc) (-t) t
  have hiAB := hiA.add hiB
  have hiABC := hiAB.add hiC
  have hsplit : (fun x : Real => qIntegrand
        (fun y => F y + c * Complex.ofReal (phiOdd y))
        (fun y => Fp y + c * Complex.ofReal (phiOddDeriv y)) x)
      = fun x : Real => qIntegrand F Fp x
        + (starRingEnd ℂ) c * xIntegrandOdd F Fp x
        + c * xIntegrandOdd (fun y => (starRingEnd ℂ) (F y))
            (fun y => (starRingEnd ℂ) (Fp y)) x
        + c * (starRingEnd ℂ) c * rIntegrandCOdd x := by
    funext x
    exact qIntegrandOdd_expansion F Fp c x
  rw [hsplit, intervalIntegral.integral_add hiABC hiD,
    intervalIntegral.integral_add hiAB hiC, intervalIntegral.integral_add hiA hiB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    xIntegralOdd_zero t F Fp hF hFc h1 h2, xIntegralOdd_conj_zero t F Fp hF hFc h1 h2,
    rIntegralOdd t]
  ring

/-- The odd envelope is odd. -/
theorem phiOdd_odd (u : Real) : phiOdd (-u) = -phiOdd u := by
  unfold phiOdd
  rw [show - -u / 2 = u / 2 from by ring]
  ring

/-- The odd envelope is positive on the positive half-line. -/
theorem phiOdd_pos (t : Real) (ht : 0 < t) : 0 < phiOdd t := by
  unfold phiOdd
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))

/-- The weight identification: `(e^t − e^{−t}) / (e^{t/2} − e^{−t/2})²
= cosh(t/2)/sinh(t/2)` — the `coth(t/2)` of the book's (8.13), stated
through `cosh`/`sinh` because Mathlib has no `coth`. -/
theorem coshHalf_div_sinhHalf_eq_ratio (t : Real) (ht : 0 < t) :
    (Real.exp t - Real.exp (-t)) / ((Real.exp (t / 2) - Real.exp (-t / 2)) ^ 2)
      = Real.cosh (t / 2) / Real.sinh (t / 2) := by
  have hab : Real.exp (t / 2) - Real.exp (-t / 2) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by linarith)))
  rw [Real.sinh_eq, Real.cosh_eq,
    show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) from by
      rw [← Real.exp_add (t / 2) (t / 2), show (t / 2 + t / 2 : Real) = t from by ring],
    show Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) from by
      rw [← Real.exp_add (-t / 2) (-t / 2), show (-t / 2 + -t / 2 : Real) = -t from by ring]]
  have hfac : Real.exp (t / 2) * Real.exp (t / 2)
      - Real.exp (-t / 2) * Real.exp (-t / 2)
      = (Real.exp (t / 2) - Real.exp (-t / 2))
        * (Real.exp (t / 2) + Real.exp (-t / 2)) := by
    ring
  rw [hfac]
  field_simp

/-- FLAGSHIP (slice 7): the odd case of (8.13) in the real-channel
shape.  For odd `Z` (`t > 0`), `Q(Z)` is the cast of a real expression
that dominates `normSq(Z(t)) · (e^t − e^{−t})/φ₋(t)²
= cosh(t/2)/sinh(t/2)·|Z(t)|²` (by `coshHalf_div_sinhHalf_eq_ratio`). -/
theorem wirtingerOdd (t : Real) (ht : 0 < t) (Z Zp : Real → Complex)
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (hZc : Continuous Zp)
    (heodd : ∀ u, Z (-u) = -Z u) :
    ∃ S : Real, 0 ≤ S ∧ (∫ x in -t..t, qIntegrand Z Zp x)
      = Complex.ofReal (Complex.normSq (Z t) * ((Real.exp t - Real.exp (-t))
          / (phiOdd t * phiOdd t)) + S) := by
  have hphi0 : Complex.ofReal (phiOdd t) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (phiOdd_pos t ht))
  set c : Complex := Z t / Complex.ofReal (phiOdd t) with hc
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
  have hphid : Continuous fun x : Real => phiOddDeriv x := by
    unfold phiOddDeriv
    exact continuous_const.mul (hR1.add hR2)
  set F : Real → Complex := fun y => Z y - c * Complex.ofReal (phiOdd y) with hFdef
  set Fp : Real → Complex := fun y => Zp y - c * Complex.ofReal (phiOddDeriv y)
    with hFpdef
  have hphiC : ∀ x, HasDerivAt (fun y : Real => c * Complex.ofReal (phiOdd y))
      (c * Complex.ofReal (phiOddDeriv x)) x := fun x =>
    HasDerivAt.const_mul c (hasDerivAt_cast (hasDerivAt_phiOdd x))
  have hFd : ∀ x, HasDerivAt F (Fp x) x := fun x => (hZ x).sub (hphiC x)
  have hFc : Continuous Fp :=
    hZc.sub (continuous_const.mul (Complex.continuous_ofReal.comp hphid))
  have h1 : F t = 0 := by
    rw [hFdef, hc]
    field_simp
    ring
  have h2 : F (-t) = 0 := by
    rw [hFdef]
    show Z (-t) - c * Complex.ofReal (phiOdd (-t)) = 0
    rw [heodd t, phiOdd_odd, Complex.ofReal_neg, hc]
    field_simp
    ring
  have hjoinV : (fun y : Real => F y + c * Complex.ofReal (phiOdd y)) = Z := by
    funext y
    rw [hFdef]
    show Z y - c * Complex.ofReal (phiOdd y) + c * Complex.ofReal (phiOdd y) = Z y
    ring
  have hjoinD : (fun y : Real => Fp y + c * Complex.ofReal (phiOddDeriv y)) = Zp := by
    funext y
    rw [hFpdef]
    show Zp y - c * Complex.ofReal (phiOddDeriv y)
        + c * Complex.ofReal (phiOddDeriv y) = Zp y
    ring
  have hshift := qShiftOdd t F Fp c hFd hFc h1 h2
  rw [hjoinV, hjoinD] at hshift
  have hreal := qF_real t F Fp hFd hFc
  refine ⟨(1 / 4 : Real) * (∫ x in -t..t, Complex.normSq (F x))
    + (∫ x in -t..t, Complex.normSq (Fp x)), sqMass_nonneg t (le_of_lt ht) F Fp, ?_⟩
  rw [hshift, hreal, Complex.mul_conj c, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    hc, Complex.normSq_div, Complex.normSq_ofReal]
  ring

end C1BombieriSection8WirtingerSlice7
end Source
end ConnesWeilRH
