/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8ExpMass
import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice3

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, twelfth slice: the Q-form of the (8.5) sum

First half of the (8.11) readback (Bombieri's Lemma 10, book
pp.209-212): the Wirtinger quadratic form of the exponential sum

```
Z(u) = Σ_γ e^{−iγu} z_γ                                     (8.5)
```

in the `qIntegrand` owner of the Wirtinger chain, read back over the
Gram pairs:

```
¼∫|Z|² + ∫|Z'|²  =  Σ_i Σ_j (¼ + γ_i γ_j) (z_i conj z_j) · winInt t (γ_j − γ_i),
```

where the derivative coefficient is `dcoef_i = (−iγ_i) z_i` — the
coordinate change behind the eigenvalue equation (7.4) — so the
off-diagonal contribution of `∫|Z'|²` is exactly `γ_i γ_j` times the
mass pair, and the diagonal `¼` rides the scalar out front.

Route: both window integrals are the slice-11 flagship
`expSum_mass_integral` (once at `z`, once at `dcoef γ z`); the
const-and-sum bookkeeping is `integral_const_mul` + `Finset.mul_sum` +
`sum_add_distrib`; the pair identity
`dcoef_i · conj(dcoef_j) = (γ_i γ_j) (z_i conj z_j)` rests on
`I * (−I) = 1` and the single-cast merge.  Continuity of `expSum`
comes free from `hasDerivAt_expSum` (everywhere differentiable
implies continuous), so no Pi-sum unfolding is ever exercised.
DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8QForm

open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open scoped ComplexConjugate
open MeasureTheory

variable {n : Nat}

/-- The derivative coefficient `w'_i = (−iγ_i) z_i` — the coefficient
vector of `Z'`, the coordinate change behind the eigenvalue equation
(7.4). -/
noncomputable def dcoef (γ : Fin n → Real) (z : Fin n → Complex)
    (i : Fin n) : Complex :=
  (Complex.ofReal (-(γ i)) * Complex.I) * z i

/-- The (8.5) sum is continuous: it is everywhere differentiable
(`hasDerivAt_expSum`), and differentiability implies continuity. -/
theorem continuous_expSum (γ : Fin n → Real) (z : Fin n → Complex) :
    Continuous (expSum γ z) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_expSum γ z x).continuousAt

/-- The pair identity of the derivative channel:
`dcoef_i · conj(dcoef_j) = (γ_i γ_j) · (z_i conj z_j)` — the
`−i`/`+i` factors multiply to `1` and the two real scalars merge into
a single cast. -/
theorem dcoef_mul_conj (γ : Fin n → Real) (z : Fin n → Complex)
    (i j : Fin n) :
    dcoef γ z i * conj (dcoef γ z j)
      = Complex.ofReal (γ i * γ j) * (z i * conj (z j)) := by
  have hI : (Complex.I * -Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  have hcast : Complex.ofReal (-(γ i)) * Complex.ofReal (-(γ j))
      = Complex.ofReal (γ i * γ j) := by
    rw [Complex.ofReal_neg, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg,
      ← Complex.ofReal_mul]
  unfold dcoef
  rw [conj_mul_d, conj_mul_d, Complex.conj_ofReal, Complex.conj_I,
    mul_mul_mul_comm (Complex.ofReal (-(γ i)) * Complex.I) (z i)
      (Complex.ofReal (-(γ j)) * -Complex.I) (conj (z j)),
    mul_mul_mul_comm (Complex.ofReal (-(γ i))) Complex.I
      (Complex.ofReal (-(γ j))) (-Complex.I),
    hI, hcast, mul_one]

/-- FLAGSHIP (slice 12a): the Wirtinger Q-form of the (8.5) sum, read
back over the Gram pairs —

```
¼∫|Z|² + ∫|Z'|² = Σ_i Σ_j (¼ + γ_i γ_j) (z_i conj z_j) · winInt t (γ_j − γ_i).
```

Both window integrals are the slice-11 flagship (once at `z`, once at
`dcoef γ z`); the derivative channel contributes `γ_i γ_j` per pair.
DETECTOR only. -/
theorem expSum_qForm (t : Real) (ht : 0 ≤ t)
    (γ : Fin n → Real) (z : Fin n → Complex) :
    ∫ x in -t..t, (Complex.ofReal ((1 / 4 : Real))
          * (expSum γ z x * conj (expSum γ z x))
        + expSum γ (dcoef γ z) x * conj (expSum γ (dcoef γ z) x))
      = ∑ i, ∑ j, Complex.ofReal ((1 / 4 : Real) + γ i * γ j)
          * (z i * conj (z j)) * winInt t (γ j - γ i) := by
  have hmass : Continuous
      (fun x : Real => expSum γ z x * conj (expSum γ z x)) :=
    (continuous_expSum γ z).mul (continuous_star.comp (continuous_expSum γ z))
  have hmassd : Continuous
      (fun x : Real => expSum γ (dcoef γ z) x * conj (expSum γ (dcoef γ z) x)) :=
    (continuous_expSum γ (dcoef γ z)).mul
      (continuous_star.comp (continuous_expSum γ (dcoef γ z)))
  have h1 : IntervalIntegrable (fun x : Real => Complex.ofReal ((1 / 4 : Real))
      * (expSum γ z x * conj (expSum γ z x))) volume (-t) t :=
    Continuous.intervalIntegrable (continuous_const.mul hmass) (-t) t
  have h2 : IntervalIntegrable (fun x : Real =>
      expSum γ (dcoef γ z) x * conj (expSum γ (dcoef γ z) x)) volume (-t) t :=
    Continuous.intervalIntegrable hmassd (-t) t
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul (Complex.ofReal ((1 / 4 : Real))),
    expSum_mass_integral t ht γ z, expSum_mass_integral t ht γ (dcoef γ z)]
  simp only [Finset.mul_sum]
  simp only [dcoef_mul_conj]
  -- Split the single double-sum on the right into the 1/4-channel and the
  -- derivative channel, pair by pair, then compare channels with the two
  -- mass expansions.  (The forward sum_add_distrib runs on the right's own
  -- binders; a backward merge across the two expansions cannot unify the
  -- distinct bound variables.)
  have hpair : ∀ a b : Fin n, Complex.ofReal ((1 / 4 : Real) + γ a * γ b)
        * (z a * conj (z b)) * winInt t (γ b - γ a)
      = Complex.ofReal ((1 / 4 : Real))
          * ((z a * conj (z b)) * winInt t (γ b - γ a))
        + Complex.ofReal (γ a * γ b) * (z a * conj (z b))
            * winInt t (γ b - γ a) := by
    intro a b
    rw [Complex.ofReal_add]
    ring
  simp only [hpair]
  rw [← Finset.sum_add_distrib (s := Finset.univ)
    (f := fun x : Fin n => ∑ y : Fin n, Complex.ofReal ((1 / 4 : Real))
        * ((z x * conj (z y)) * winInt t (γ y - γ x)))
    (g := fun x : Fin n => ∑ y : Fin n, Complex.ofReal (γ x * γ y)
        * (z x * conj (z y)) * winInt t (γ y - γ x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Finset.sum_add_distrib (s := Finset.univ)
    (f := fun y : Fin n => Complex.ofReal ((1 / 4 : Real))
        * ((z x * conj (z y)) * winInt t (γ y - γ x)))
    (g := fun y : Fin n => Complex.ofReal (γ x * γ y)
        * (z x * conj (z y)) * winInt t (γ y - γ x))).symm

/-- The same readback in the `qIntegrand` owner of the Wirtinger
chain — the exact integrand `wirtingerFull` consumes, with the
derivative slot filled by the (8.5) sum at `dcoef γ z`
(`hasDerivAt_expSum` identifies it with the true derivative). -/
theorem expSum_qIntegrand_mass (t : Real) (ht : 0 ≤ t)
    (γ : Fin n → Real) (z : Fin n → Complex) :
    ∫ x in -t..t, qIntegrand (expSum γ z) (expSum γ (dcoef γ z)) x
      = ∑ i, ∑ j, Complex.ofReal ((1 / 4 : Real) + γ i * γ j)
          * (z i * conj (z j)) * winInt t (γ j - γ i) := by
  unfold qIntegrand
  exact expSum_qForm t ht γ z

end C1BombieriSection8QForm
end Source
end ConnesWeilRH
