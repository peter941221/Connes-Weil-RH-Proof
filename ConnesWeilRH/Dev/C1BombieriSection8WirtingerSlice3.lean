/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice2

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), third slice: the Q-shift identity

The quadratic form of Bombieri's Lemma 10 (book pp.209-212),

```
Q(g) = ¼∫_{−t}^{t} g·conj(g) + ∫_{−t}^{t} g'·conj(g')
```

shifts cleanly when `g` is replaced by `F + c·φ₊` with the SAME constant
`R = e^t − e^{−t}` of slice 2: the pointwise expansion is

```
Qint(g) = Qint(F) + conj(c)·Xint(F) + c·Xint(conj F) + |c|²·Rint
```

where `Xint` is exactly the integrand of the IBP core (slice 1).  Since
`φ₊` is real-valued, `conj φ₊ = φ₊`, and since `F(±t) = 0` the two IBP
integrals vanish (`ibpCoreEven_zero`), leaving

```
Q(F + c·φ₊) = Q(F) + c·conj(c)·(e^t − e^{−t}).
```

Mathlib note: `conj` has NO `HasDerivAt` over `ℝ` (a `HasDerivAt`
derivative is multiplication by a complex scalar, which `conj` is not),
so the conjugated cross integral is handled at the INTEGRAL level: the
root-level `integral_conj` (Bochner) applies to each `Ioc` piece of the
interval-integral definition.  No numerical datum enters any leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerSlice3

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice2
open MeasureTheory

/-- Conjugation fixes real scalars in `ℂ` (stated with a bare variable so
that `binop%` cannot lift the argument into the complex ambient). -/
theorem star_ofReal (r : Real) :
    (starRingEnd ℂ) (Complex.ofReal r) = Complex.ofReal r := by simp

/-- The IBP-core integrand: exactly the integrand of `ibpCoreEven`. -/
private noncomputable def xIntegrand (f fp : Real → Complex) (x : Real) : Complex :=
  fp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2)))
    + f x * Complex.ofReal ((1 / 4 : Real) * phiEven x)

/-- The Q-form integrand. -/
private noncomputable def qIntegrand (f fp : Real → Complex) (x : Real) : Complex :=
  Complex.ofReal ((1 / 4 : Real)) * (f x * (starRingEnd ℂ) (f x))
    + fp x * (starRingEnd ℂ) (fp x)

/-- The R-form integrand (the envelope quadratic density). -/
private noncomputable def rIntegrandC (x : Real) : Complex :=
  Complex.ofReal ((1 / 4 : Real)) * (Complex.ofReal (phiEven x) * Complex.ofReal (phiEven x))
    + Complex.ofReal (phiEvenDeriv x) * Complex.ofReal (phiEvenDeriv x)

/-- Conjugation passes through the interval integral (root-level Bochner
lemma applied to each `Ioc` piece of the interval-integral definition). -/
theorem integral_star_interval (a b : Real) (J : Real → Complex) :
    ∫ x in a..b, (starRingEnd ℂ) (J x) = (starRingEnd ℂ) (∫ x in a..b, J x) := by
  show ((∫ x in Set.Ioc a b, (starRingEnd ℂ) (J x) ∂volume)
      - ∫ x in Set.Ioc b a, (starRingEnd ℂ) (J x) ∂volume)
    = (starRingEnd ℂ) ((∫ x in Set.Ioc a b, J x ∂volume)
      - ∫ x in Set.Ioc b a, J x ∂volume)
  rw [integral_conj, integral_conj, map_sub]

/-- `Xint(conj F) = conj(Xint(F))` pointwise: the weights are real. -/
theorem xIntegrand_conj (F Fp : Real → Complex) (x : Real) :
    xIntegrand (fun y => (starRingEnd ℂ) (F y)) (fun y => (starRingEnd ℂ) (Fp y)) x
      = (starRingEnd ℂ) (xIntegrand F Fp x) := by
  unfold xIntegrand
  rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    star_ofReal, star_ofReal]

/-- The IBP-core integral vanishes at zero endpoints (readback through
the `xIntegrand` definitional form). -/
theorem xIntegral_zero (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    ∫ x in -t..t, xIntegrand F Fp x = 0 :=
  ibpCoreEven_zero t F Fp hF hFc h1 h2

/-- The conjugated IBP-core integral also vanishes: no `HasDerivAt`
through `conj` is needed, only the integral-level transport. -/
theorem xIntegral_conj_zero (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    ∫ x in -t..t, xIntegrand (fun y => (starRingEnd ℂ) (F y))
        (fun y => (starRingEnd ℂ) (Fp y)) x = 0 := by
  have hpt : (fun x : Real => xIntegrand (fun y => (starRingEnd ℂ) (F y))
      (fun y => (starRingEnd ℂ) (Fp y)) x)
      = fun x : Real => (starRingEnd ℂ) (xIntegrand F Fp x) := by
    funext x
    exact xIntegrand_conj F Fp x
  rw [hpt, integral_star_interval, xIntegral_zero t F Fp hF hFc h1 h2, map_zero]

/-- The R-integral through the real channel: `∫ rIntegrandC = e^t − e^{−t}`. -/
theorem rIntegral (t : Real) :
    ∫ x in -t..t, rIntegrandC x = Complex.ofReal (Real.exp t - Real.exp (-t)) := by
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
  have hphi : Continuous fun x : Real => phiEven x := by
    unfold phiEven
    exact hR1.add hR2
  have hphid : Continuous fun x : Real => phiEvenDeriv x := by
    unfold phiEvenDeriv
    exact continuous_const.mul (hR1.sub hR2)
  have hA : IntervalIntegrable (fun x : Real => (1 / 4 : Real) * (phiEven x * phiEven x))
      volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul (hphi.mul hphi)) (-t) t
  have hB : IntervalIntegrable (fun x : Real => phiEvenDeriv x * phiEvenDeriv x)
      volume (-t) t := Continuous.intervalIntegrable (hphid.mul hphid) (-t) t
  have hfun : (fun x : Real => rIntegrandC x)
      = fun x : Real => Complex.ofReal ((1 / 4 : Real) * (phiEven x * phiEven x)
          + phiEvenDeriv x * phiEvenDeriv x) := by
    funext x
    unfold rIntegrandC
    rw [← Complex.ofReal_mul (phiEven x) (phiEven x),
      ← Complex.ofReal_mul ((1 : Real) / 4) (phiEven x * phiEven x),
      ← Complex.ofReal_mul (phiEvenDeriv x) (phiEvenDeriv x), ← Complex.ofReal_add]
  rw [hfun, intervalIntegral.integral_ofReal, intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_const_mul, envelopeIntegralEven]

/-- The pointwise Q-shift expansion: the Q-integrand of `F + c·φ₊` is the
Q-integrand of `F`, plus the two (conjugated) IBP-core integrands, plus
`c·conj(c)` times the envelope quadratic density. -/
theorem qIntegrand_expansion (F Fp : Real → Complex) (c : Complex) (x : Real) :
    qIntegrand (fun y => F y + c * Complex.ofReal (phiEven y))
        (fun y => Fp y + c * Complex.ofReal (phiEvenDeriv y)) x
      = qIntegrand F Fp x
        + (starRingEnd ℂ) c * xIntegrand F Fp x
        + c * xIntegrand (fun y => (starRingEnd ℂ) (F y))
            (fun y => (starRingEnd ℂ) (Fp y)) x
        + c * (starRingEnd ℂ) c * rIntegrandC x := by
  unfold qIntegrand xIntegrand rIntegrandC phiEvenDeriv
  rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ),
    star_ofReal, star_ofReal,
    Complex.ofReal_mul ((1 : Real) / 4) (phiEven x)]
  ring

/-- FLAGSHIP (slice 3): the Q-shift identity.  With `F(±t) = 0` the two
IBP-core cross integrals vanish, so the quadratic form of `F + c·φ₊` is
that of `F` plus `c·conj(c)·(e^t − e^{−t})` — the constant `R = 2 sinh t`
of the book's (8.13) chain. -/
theorem qShiftEven (t : Real) (F Fp : Real → Complex) (c : Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    (∫ x in -t..t, qIntegrand (fun y => F y + c * Complex.ofReal (phiEven y))
        (fun y => Fp y + c * Complex.ofReal (phiEvenDeriv y)) x)
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
  have hphi : Continuous fun x : Real => phiEven x := by
    unfold phiEven
    exact hR1.add hR2
  have hphid : Continuous fun x : Real => phiEvenDeriv x := by
    unfold phiEvenDeriv
    exact continuous_const.mul (hR1.sub hR2)
  have hphiEc : Continuous fun x : Real =>
      Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2))) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (hR1.sub hR2))
  have hphiEc0 : Continuous fun x : Real => Complex.ofReal (phiEven x) :=
    Complex.continuous_ofReal.comp hphi
  have hphiEc2 : Continuous fun x : Real =>
      Complex.ofReal ((1 / 4 : Real) * phiEven x) :=
    Complex.continuous_ofReal.comp (continuous_const.mul hphi)
  have hIc : Continuous fun x : Real => xIntegrand F Fp x := by
    unfold xIntegrand
    exact (hFc.mul hphiEc).add (hFcont.mul hphiEc2)
  have hAc : Continuous fun x : Real => qIntegrand F Fp x := by
    unfold qIntegrand
    exact (continuous_const.mul (hFcont.mul (hstar _ hFcont))).add
      (hFc.mul (hstar _ hFc))
  have hCc : Continuous fun x : Real =>
      xIntegrand (fun y => (starRingEnd ℂ) (F y)) (fun y => (starRingEnd ℂ) (Fp y)) x := by
    unfold xIntegrand
    exact ((hstar _ hFc).mul hphiEc).add ((hstar _ hFcont).mul hphiEc2)
  have hDc : Continuous fun x : Real => rIntegrandC x := by
    unfold rIntegrandC phiEvenDeriv
    exact (continuous_const.mul (hphiEc0.mul hphiEc0)).add (hphiEc.mul hphiEc)
  have hiA : IntervalIntegrable (fun x : Real => qIntegrand F Fp x) volume (-t) t :=
    Continuous.intervalIntegrable hAc (-t) t
  have hiB : IntervalIntegrable
      (fun x : Real => (starRingEnd ℂ) c * xIntegrand F Fp x) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hIc) (-t) t
  have hiC : IntervalIntegrable
      (fun x : Real => c * xIntegrand (fun y => (starRingEnd ℂ) (F y))
        (fun y => (starRingEnd ℂ) (Fp y)) x) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hCc) (-t) t
  have hiD : IntervalIntegrable
      (fun x : Real => c * (starRingEnd ℂ) c * rIntegrandC x) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hDc) (-t) t
  have hiAB := hiA.add hiB
  have hiABC := hiAB.add hiC
  have hsplit : (fun x : Real => qIntegrand
        (fun y => F y + c * Complex.ofReal (phiEven y))
        (fun y => Fp y + c * Complex.ofReal (phiEvenDeriv y)) x)
      = fun x : Real => qIntegrand F Fp x
        + (starRingEnd ℂ) c * xIntegrand F Fp x
        + c * xIntegrand (fun y => (starRingEnd ℂ) (F y))
            (fun y => (starRingEnd ℂ) (Fp y)) x
        + c * (starRingEnd ℂ) c * rIntegrandC x := by
    funext x
    exact qIntegrand_expansion F Fp c x
  rw [hsplit, intervalIntegral.integral_add hiABC hiD,
    intervalIntegral.integral_add hiAB hiC, intervalIntegral.integral_add hiA hiB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    xIntegral_zero t F Fp hF hFc h1 h2, xIntegral_conj_zero t F Fp hF hFc h1 h2,
    rIntegral t]
  ring

end C1BombieriSection8WirtingerSlice3
end Source
end ConnesWeilRH
