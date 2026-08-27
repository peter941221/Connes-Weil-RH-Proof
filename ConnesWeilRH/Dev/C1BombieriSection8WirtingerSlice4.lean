/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice3

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), fourth slice: Q(F) is real and nonnegative

The Q-form of a function with zero endpoints is REAL and NONNEGATIVE —
the real channel of the book's proof of Lemma 10 (pp.209-212).  Since
`ℂ` carries no order, the fact is stated as the pair

* `qF_real`      — `Q(F)` equals the cast of an explicit real integral
                   expression (`¼∫‖F‖² + ∫‖F'‖²`, via `Complex.mul_conj`);
* `sqMass_nonneg` — that real expression is `≥ 0` (both summands are:
                   `Complex.normSq` is pointwise nonnegative and the
                   half-weight is positive).

Together they feed the even-case Wirtinger inequality through the
Q-shift identity `qShiftEven`.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerSlice4

open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open MeasureTheory

/-- The Q-form of `F` is the cast of a real integral expression: the
pointwise products `F · conj(F)` and `F' · conj(F')` collapse to
`Complex.normSq` casts, and the whole integral passes through the real
channel (`integral_ofReal`). -/
theorem qF_real (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp) :
    (∫ x in -t..t, qIntegrand F Fp x)
      = Complex.ofReal ((1 / 4 : Real) * (∫ x in -t..t, Complex.normSq (F x))
        + (∫ x in -t..t, Complex.normSq (Fp x))) := by
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    fun x => (hF x).continuousAt
  have hA : IntervalIntegrable
      (fun x : Real => (1 / 4 : Real) * Complex.normSq (F x)) volume (-t) t :=
    Continuous.intervalIntegrable
      (continuous_const.mul (Complex.continuous_normSq.comp hFcont)) (-t) t
  have hB : IntervalIntegrable (fun x : Real => Complex.normSq (Fp x))
      volume (-t) t :=
    Continuous.intervalIntegrable (Complex.continuous_normSq.comp hFc) (-t) t
  have hfun : (fun x : Real => qIntegrand F Fp x)
      = fun x : Real => Complex.ofReal ((1 / 4 : Real) * Complex.normSq (F x)
          + Complex.normSq (Fp x)) := by
    funext x
    unfold qIntegrand
    rw [Complex.mul_conj, Complex.mul_conj,
      ← Complex.ofReal_mul ((1 : Real) / 4) (Complex.normSq (F x)),
      ← Complex.ofReal_add]
  rw [hfun, intervalIntegral.integral_ofReal, intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_const_mul]

/-- The real channel expression of `Q(F)` is nonnegative for `t ≥ 0`:
both summands are nonnegative (`Complex.normSq` pointwise, half-weight
positive) and `intervalIntegral.integral_nonneg` needs `-t ≤ t`. -/
theorem sqMass_nonneg (t : Real) (ht : 0 ≤ t) (F Fp : Real → Complex) :
    0 ≤ (1 / 4 : Real) * (∫ x in -t..t, Complex.normSq (F x))
      + (∫ x in -t..t, Complex.normSq (Fp x)) := by
  refine add_nonneg (mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg (by linarith)
      (fun x _ => Complex.normSq_nonneg (F x))))
    (intervalIntegral.integral_nonneg (by linarith)
      (fun x _ => Complex.normSq_nonneg (Fp x)))

end C1BombieriSection8WirtingerSlice4
end Source
end ConnesWeilRH
