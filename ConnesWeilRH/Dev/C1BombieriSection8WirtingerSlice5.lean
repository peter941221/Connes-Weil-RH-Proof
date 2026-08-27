/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice4

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), fifth slice: the even-case inequality

The even case of the Wirtinger-type inequality (8.13) of Bombieri's
Lemma 10 (book pp.209-212): for a C¹ EVEN function `Z` on `[-t, t]`,

```
Q(Z) = ↑( normSq(Z(t)) · (e^t − e^{−t}) / φ₊(t)² + S ),   S ≥ 0,
```

and since `(e^t − e^{−t}) / (e^{t/2} + e^{−t/2})² = tanh(t/2)`, this is
exactly `Q(Z) ≥ tanh(t/2)·|Z(t)|²` in the real-channel shape forced by
the orderless `ℂ`.

Mechanism: subtract `c := Z(t)/φ₊(t)` times the envelope from `Z`;
the remainder `F` is C¹, even (φ₊ is even), and vanishes at both
endpoints, so `qShiftEven` applies and `qF_real` + `sqMass_nonneg`
push `Q(F)` through the real channel.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerSlice5

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice2
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice4
open MeasureTheory

/-- The even envelope is even. -/
theorem phiEven_even (u : Real) : phiEven (-u) = phiEven u := by
  unfold phiEven
  rw [show - -u / 2 = u / 2 from by ring]
  ring

/-- The even envelope never vanishes. -/
theorem phiEven_ne_zero (u : Real) : phiEven u ≠ 0 :=
  ne_of_gt (add_pos (Real.exp_pos (u / 2)) (Real.exp_pos (-u / 2)))

/-- The weight identification: `(e^t − e^{−t}) / (e^{t/2} + e^{−t/2})²
= tanh(t/2)` — the `tanh(t/2)` of the book's (8.13). -/
theorem tanhHalf_eq_ratio (t : Real) :
    (Real.exp t - Real.exp (-t)) / ((Real.exp (t / 2) + Real.exp (-t / 2)) ^ 2)
      = Real.tanh (t / 2) := by
  have hab : Real.exp (t / 2) + Real.exp (-t / 2) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos (t / 2)) (Real.exp_pos (-t / 2)))
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq,
    show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) from by
      rw [← Real.exp_add (t / 2) (t / 2), show (t / 2 + t / 2 : Real) = t from by ring],
    show Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) from by
      rw [← Real.exp_add (-t / 2) (-t / 2), show (-t / 2 + -t / 2 : Real) = -t from by ring]]
  field_simp
  ring

/-- FLAGSHIP (slice 5): the even case of (8.13) in the real-channel
shape.  For even `Z`, `Q(Z)` is the cast of a real expression that
dominates `normSq(Z(t)) · (e^t − e^{−t})/φ₊(t)² = tanh(t/2)·|Z(t)|²`
(by `tanhHalf_eq_ratio`). -/
theorem wirtingerEven (t : Real) (ht : 0 ≤ t) (Z Zp : Real → Complex)
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (hZc : Continuous Zp)
    (heven : ∀ u, Z (-u) = Z u) :
    ∃ S : Real, 0 ≤ S ∧ (∫ x in -t..t, qIntegrand Z Zp x)
      = Complex.ofReal (Complex.normSq (Z t) * ((Real.exp t - Real.exp (-t))
          / (phiEven t * phiEven t)) + S) := by
  have hphi0 : Complex.ofReal (phiEven t) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (phiEven_ne_zero t)
  set c : Complex := Z t / Complex.ofReal (phiEven t) with hc
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
  have hphid : Continuous fun x : Real => phiEvenDeriv x := by
    unfold phiEvenDeriv
    exact continuous_const.mul (hR1.sub hR2)
  set F : Real → Complex := fun y => Z y - c * Complex.ofReal (phiEven y) with hFdef
  set Fp : Real → Complex := fun y => Zp y - c * Complex.ofReal (phiEvenDeriv y)
    with hFpdef
  have hphiC : ∀ x, HasDerivAt (fun y : Real => c * Complex.ofReal (phiEven y))
      (c * Complex.ofReal (phiEvenDeriv x)) x := fun x =>
    HasDerivAt.const_mul c (hasDerivAt_cast (hasDerivAt_phiEven x))
  have hFd : ∀ x, HasDerivAt F (Fp x) x := fun x => (hZ x).sub (hphiC x)
  have hFc : Continuous Fp :=
    hZc.sub (continuous_const.mul (Complex.continuous_ofReal.comp hphid))
  have h1 : F t = 0 := by
    rw [hFdef, hc]
    field_simp
    ring
  have h2 : F (-t) = 0 := by
    rw [hFdef]
    show Z (-t) - c * Complex.ofReal (phiEven (-t)) = 0
    rw [heven t, phiEven_even, hc]
    field_simp
    ring
  have hjoinV : (fun y : Real => F y + c * Complex.ofReal (phiEven y)) = Z := by
    funext y
    rw [hFdef]
    show Z y - c * Complex.ofReal (phiEven y) + c * Complex.ofReal (phiEven y) = Z y
    ring
  have hjoinD : (fun y : Real => Fp y + c * Complex.ofReal (phiEvenDeriv y)) = Zp := by
    funext y
    rw [hFpdef]
    show Zp y - c * Complex.ofReal (phiEvenDeriv y)
        + c * Complex.ofReal (phiEvenDeriv y) = Zp y
    ring
  have hshift := qShiftEven t F Fp c hFd hFc h1 h2
  rw [hjoinV, hjoinD] at hshift
  have hreal := qF_real t F Fp hFd hFc
  refine ⟨(1 / 4 : Real) * (∫ x in -t..t, Complex.normSq (F x))
    + (∫ x in -t..t, Complex.normSq (Fp x)), sqMass_nonneg t ht F Fp, ?_⟩
  rw [hshift, hreal, Complex.mul_conj c, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    hc, Complex.normSq_div, Complex.normSq_ofReal]
  ring

end C1BombieriSection8WirtingerSlice5
end Source
end ConnesWeilRH
