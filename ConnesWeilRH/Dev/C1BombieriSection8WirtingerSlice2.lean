/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8Wirtinger

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), second slice: the envelope integral and X(F) = 0

Two building blocks toward the Wirtinger-type inequality (8.13) of
Bombieri's Lemma 10 (book pp.209-212):

* the envelope quadratic integral `R = ¼∫φ₊² + ∫φ₊'² = e^t − e^{−t}`
  (= `2 sinh t`): the pointwise square expansions
  `φ₊(u)² = e^u + 2 + e^{−u}` and `φ₊'(u)² = ¼(e^u − 2 + e^{−u})` turn the
  two integrals into elementary exponential integrals, whose `t`-terms
  cancel — this is the constant `R` in the Q-shift identity
  `Q(g) = Q(F) + |c|²·R`;
* the vanishing of the IBP core on functions with zero endpoints:
  `F(±t) = 0` forces `X(F) = ¼∫φ₊F + ∫φ₊'F' = 0` — the fact that kills the
  cross terms of the Q-shift identity.

No numerical datum enters any leaf: only exact identities.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerSlice2

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open MeasureTheory

/-- The derivative `φ₊'(u) = ½(e^{u/2} − e^{−u/2})` as a named function. -/
noncomputable def phiEvenDeriv (u : Real) : Real :=
  (1 / 2 : Real) * (Real.exp (u / 2) - Real.exp (-u / 2))

/-- The real exponential integral over any interval, via the fundamental
theorem (Mathlib has no `intervalIntegral.integral_exp`). -/
private theorem integral_exp_real (a b : Real) :
    ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => Real.hasDerivAt_exp x)
    (Continuous.intervalIntegrable Real.continuous_exp a b)

/-- The reflected exponential integral; the sign flip is baked in. -/
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

/-- The pointwise square of the even envelope. -/
theorem phiEven_sq (u : Real) :
    phiEven u * phiEven u = Real.exp u + 2 + Real.exp (-u) := by
  unfold phiEven
  rw [show (Real.exp (u / 2) + Real.exp (-u / 2))
        * (Real.exp (u / 2) + Real.exp (-u / 2))
      = Real.exp (u / 2) * Real.exp (u / 2)
        + 2 * (Real.exp (u / 2) * Real.exp (-u / 2))
        + Real.exp (-u / 2) * Real.exp (-u / 2) from by ring,
    expHalf_mul_expHalf, expHalf_mul_expNegHalf, expNegHalf_mul_expNegHalf]
  ring

/-- The pointwise square of the envelope derivative. -/
theorem phiEvenDeriv_sq (u : Real) :
    phiEvenDeriv u * phiEvenDeriv u
      = (1 / 4 : Real) * (Real.exp u - 2 + Real.exp (-u)) := by
  unfold phiEvenDeriv
  rw [show ((1 / 2 : Real) * (Real.exp (u / 2) - Real.exp (-u / 2)))
        * ((1 / 2 : Real) * (Real.exp (u / 2) - Real.exp (-u / 2)))
      = (1 / 4 : Real) * (Real.exp (u / 2) * Real.exp (u / 2)
          - 2 * (Real.exp (u / 2) * Real.exp (-u / 2))
          + Real.exp (-u / 2) * Real.exp (-u / 2)) from by ring,
    expHalf_mul_expHalf, expHalf_mul_expNegHalf, expNegHalf_mul_expNegHalf]
  ring

/-- The IBP core vanishes on functions with zero endpoints — the fact
that kills the cross terms of the Q-shift identity. -/
theorem ibpCoreEven_zero (t : Real) (F Fp : Real → Complex)
    (hF : ∀ x, HasDerivAt F (Fp x) x) (hFc : Continuous Fp)
    (h1 : F t = 0) (h2 : F (-t) = 0) :
    ∫ x in -t..t,
        (Fp x * Complex.ofReal
            ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2)))
          + F x * Complex.ofReal ((1 / 4 : Real) * phiEven x))
      = 0 := by
  have h := ConnesWeilRH.Source.C1BombieriSection8Wirtinger.ibpCoreEven t F Fp hF hFc
  rw [h1, h2] at h
  simpa using h

/-- The envelope quadratic integral `R := ¼∫φ₊² + ∫φ₊'²` over `[−t, t]`
equals `e^t − e^{−t}` (= `2 sinh t`): the `t`-terms of the two square
expansions cancel. -/
theorem envelopeIntegralEven (t : Real) :
    (1 / 4 : Real) * (∫ x in -t..t, phiEven x * phiEven x)
      + (∫ x in -t..t, phiEvenDeriv x * phiEvenDeriv x)
      = Real.exp t - Real.exp (-t) := by
  have hf : (fun x : Real => phiEven x * phiEven x)
      = fun x : Real => Real.exp x + 2 + Real.exp (-x) := by
    funext x
    exact phiEven_sq x
  have hg : (fun x : Real => phiEvenDeriv x * phiEvenDeriv x)
      = fun x : Real => (1 / 4 : Real) * (Real.exp x - 2 + Real.exp (-x)) := by
    funext x
    exact phiEvenDeriv_sq x
  have hA : IntervalIntegrable (fun x : Real => Real.exp x) volume (-t) t :=
    Continuous.intervalIntegrable Real.continuous_exp (-t) t
  have hN : IntervalIntegrable (fun x : Real => Real.exp (-x)) volume (-t) t :=
    Continuous.intervalIntegrable (Real.continuous_exp.comp continuous_neg) (-t) t
  have hC : IntervalIntegrable (fun _ : Real => (2 : Real)) volume (-t) t :=
    Continuous.intervalIntegrable continuous_const (-t) t
  have hA2 : IntervalIntegrable (fun x : Real => Real.exp x + 2) volume (-t) t :=
    hA.add hC
  have hSub2 : IntervalIntegrable (fun x : Real => Real.exp x - 2) volume (-t) t :=
    hA.sub hC
  rw [hf, hg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hSub2 hN,
    intervalIntegral.integral_sub hA hC,
    intervalIntegral.integral_const (2 : Real),
    intervalIntegral.integral_add hA2 hN,
    intervalIntegral.integral_add hA hC,
    intervalIntegral.integral_const (2 : Real),
    integral_exp_real, integral_expNeg_real]
  simp only [smul_eq_mul]
  ring

end C1BombieriSection8WirtingerSlice2
end Source
end ConnesWeilRH
