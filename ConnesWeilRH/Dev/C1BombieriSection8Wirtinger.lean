/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8Boundary

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), first slice: the IBP core identity

Bombieri's Lemma 10 (book pp.209-212) finishes through the Wirtinger-type
inequality (8.13): for a `C¹` function on `[−t, t]` with even/odd endpoint
symmetry, the quadratic form

```
Q(g) = ¼∫_{−t}^{t} |g|² + ∫_{−t}^{t} |g'|²
```

dominates `tanh(t/2)·|g(t)|²` (even case) resp. `coth(t/2)·|g(t)|²` (odd
case), with equality exactly on `e^{u/2} ± e^{−u/2}`.  The Lean proof is
built entirely from explicit identities; the skeleton established in this
session (recorded in `docs/proofs/1043` section 6y) is:

* envelopes `φ_±(u) = e^{u/2} ± e^{−u/2}` with `φ'' = ¼φ`;
* the integration-by-parts core `X(h) := ¼∫φh + ∫φ'h' = [hφ']_{−t}^{t}`;
* for `c = g(t)/φ(t)` and `F = g − cφ` (so `F(±t) = 0`), the cross terms
  of `Q(g) − Q(F) = conj c·X(F) + c·conj(X(F)) + |c|²·R` vanish because
  `X(F) = 0`, leaving `Q(g) = Q(F) + |c|²·2 sinh t = Q(F) + K·|g(t)|²`
  with `K = tanh(t/2)` (even) resp. `coth(t/2)` (odd);
* `Q(F) = ∫ (¼|F|² + |F'|²) ≥ 0` through the real-channel
  `intervalIntegral.integral_ofReal`.

This first slice lands the envelopes with their derivative/ODE facts and
the IBP core identity for a `C¹` complex-valued `g` against the even
envelope.  No numerical datum enters any leaf: only exact identities.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8Wirtinger

/-- The even envelope `φ₊(u) = e^{u/2} + e^{−u/2} = 2 cosh(u/2)`. -/
noncomputable def phiEven (u : Real) : Real := Real.exp (u / 2) + Real.exp (-u / 2)

/-- Derivative of `y ↦ y / 2`. -/
theorem hasDerivAt_half (u : Real) :
    HasDerivAt (fun y : Real => y / 2) ((1 : Real) / 2) u := by
  have hrw : (fun y : Real => y / 2) = fun y : Real => (1 / 2 : Real) * y := by
    funext y
    ring
  rw [hrw]
  simpa only [id_eq, mul_one] using HasDerivAt.const_mul (1 / 2) (hasDerivAt_id u)

/-- Derivative of `y ↦ -y / 2`. -/
theorem hasDerivAt_negHalf (u : Real) :
    HasDerivAt (fun y : Real => -y / 2) ((-1 : Real) / 2) u := by
  have hrw : (fun y : Real => -y / 2) = fun y : Real => (-1 / 2 : Real) * y := by
    funext y
    ring
  rw [hrw]
  simpa only [id_eq, mul_one] using HasDerivAt.const_mul (-1 / 2) (hasDerivAt_id u)

/-- `e^{y/2}` has derivative `½ e^{u/2}` at `u`. -/
theorem hasDerivAt_expHalf (u : Real) :
    HasDerivAt (fun y : Real => Real.exp (y / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
  have hcomp : HasDerivAt (Real.exp ∘ fun y : Real => y / 2)
      (Real.exp (u / 2) * (1 / 2)) u :=
    (Real.hasDerivAt_exp (u / 2)).comp u (hasDerivAt_half u)
  exact hcomp

/-- `e^{-y/2}` has derivative `−½ e^{−u/2}` at `u`. -/
theorem hasDerivAt_expNegHalf (u : Real) :
    HasDerivAt (fun y : Real => Real.exp (-y / 2)) (Real.exp (-u / 2) * (-1 / 2)) u := by
  have hcomp : HasDerivAt (Real.exp ∘ fun y : Real => -y / 2)
      (Real.exp (-u / 2) * (-1 / 2)) u :=
    (Real.hasDerivAt_exp (-u / 2)).comp u (hasDerivAt_negHalf u)
  exact hcomp

/-- Derivative transport through the `Real → ℂ` cast. -/
theorem hasDerivAt_cast {r : Real → Real} {x : Real} {rv : Real}
    (h : HasDerivAt r rv x) :
    HasDerivAt (fun y : Real => ((r y : Real) : Complex)) (((rv : Real) : Complex)) x := by
  refine HasDerivAt.scomp x (Complex.ofRealCLM.hasDerivAt) h |>.congr_deriv ?_
  show ((rv : Real) : Complex) • Complex.ofRealCLM 1 = ((rv : Real) : Complex)
  rw [show (Complex.ofRealCLM 1 : Complex) = 1 from rfl, smul_eq_mul, mul_one]

/-- `φ₊` has derivative `½(e^{u/2} − e^{−u/2})` — purely in `ℝ`. -/
theorem hasDerivAt_phiEven (u : Real) :
    HasDerivAt phiEven ((1 / 2 : Real) * (Real.exp (u / 2) - Real.exp (-u / 2))) u :=
  HasDerivAt.add (hasDerivAt_expHalf u) (hasDerivAt_expNegHalf u) |>.congr_deriv (by ring)

/-- The envelope ODE: `φ₊'' = ¼ φ₊`. -/
theorem phiEven_ode (u : Real) :
    HasDerivAt (fun y : Real => (1 / 2 : Real) * (Real.exp (y / 2) - Real.exp (-y / 2)))
      ((1 / 4 : Real) * phiEven u) u := by
  have hrw : (fun y : Real => (1 / 2 : Real) * (Real.exp (y / 2) - Real.exp (-y / 2)))
      = fun y : Real => (1 / 2 : Real) * Real.exp (y / 2)
          - (1 / 2 : Real) * Real.exp (-y / 2) := by
    funext y
    ring
  rw [hrw]
  refine HasDerivAt.sub
    (HasDerivAt.const_mul (1 / 2) (hasDerivAt_expHalf u))
    (HasDerivAt.const_mul (1 / 2) (hasDerivAt_expNegHalf u)) |>.congr_deriv ?_
  unfold phiEven
  ring

/-- The complexified envelope derivative carries the ODE: the product
`g · φ₊'` (with `g` complex-valued) has derivative `g'·φ₊' + g·(¼φ₊)`.
Every cast is a single `Complex.ofReal` of a real-typed product, so the
statement matches the `hasDerivAt_cast` output form syntactically. -/
theorem hasDerivAt_g_mul_phiEven' (g gp : Real → Complex) (x : Real)
    (hg : HasDerivAt g (gp x) x) :
    HasDerivAt (fun y : Real =>
        g y * Complex.ofReal ((1 / 2 : Real) * (Real.exp (y / 2) - Real.exp (-y / 2))))
      (gp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2)))
        + g x * Complex.ofReal ((1 / 4 : Real) * phiEven x)) x := by
  refine HasDerivAt.mul hg (hasDerivAt_cast (phiEven_ode x)) |>.congr_deriv ?_
  ring

/-- The IBP core identity: for a `C¹` complex-valued `g` on `[−t, t]` and
the even envelope, `¼∫φ₊g + ∫φ₊'g' = [gφ₊']_{−t}^{t}` — the product-rule
derivative integrated through the fundamental theorem. -/
theorem ibpCoreEven (t : Real) (g gp : Real → Complex)
    (hg : ∀ x, HasDerivAt g (gp x) x) (hgc : Continuous gp) :
    ∫ x in -t..t,
        (gp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2)))
          + g x * Complex.ofReal ((1 / 4 : Real) * phiEven x))
      = g t * Complex.ofReal ((1 / 2 : Real) * (Real.exp (t / 2) - Real.exp (-t / 2)))
        - g (-t) * Complex.ofReal
            ((1 / 2 : Real) * (Real.exp (-t / 2) - Real.exp (t / 2))) := by
  -- Real-channel continuity building blocks; every negative literal carries
  -- an explicit `: Real` ascription so it cannot fall through to `ℤ`.
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
      Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2))) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (hR1.sub hR2))
  have hphiE : Continuous fun x : Real =>
      Complex.ofReal ((1 / 4 : Real) * phiEven x) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (hR1.add hR2))
  have hgCont : Continuous g := continuous_iff_continuousAt.mpr
    fun x => (hg x).continuousAt
  have hcont : Continuous fun x : Real =>
      gp x * Complex.ofReal ((1 / 2 : Real) * (Real.exp (x / 2) - Real.exp (-x / 2)))
        + g x * Complex.ofReal ((1 / 4 : Real) * phiEven x) :=
    (hgc.mul hgcE).add (hgCont.mul hphiE)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_g_mul_phiEven' g gp x (hg x))
    (Continuous.intervalIntegrable hcont (-t) t)
  -- At the endpoint `-t` the specialized derivative carries `- -t`; normalize.
  rw [neg_neg] at hmain
  exact hmain

end C1BombieriSection8Wirtinger
end Source
end ConnesWeilRH
