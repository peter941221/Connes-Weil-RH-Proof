/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8QForm

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, thirteenth slice: the boundary bridge

Second brick of the (8.11) readback (Bombieri's Lemma 10, book
pp.209-212): the weighted double sum that separates the sinc channel
of the Q-form from the Gram matrix, factored into boundary products.
The identity engine is

```
θ · winInt t θ = 2 sin(θt)   and   −2 sin a = I (e^{ia} − e^{−ia}),
```

so each pair `γ_i (γ_i − γ_j) winInt t (γ_j − γ_i)` collapses to
`I (e^{i(γ_j−γ_i)t} − e^{−i(γ_j−γ_i)t})`, and the exponential
`e^{i(γ_j−γ_i)t} = e^{iγ_j t} · conj(e^{iγ_i t})` splits the double
sum into the product of two single sums:

```
ΣΣ γ_i(γ_i−γ_j) winInt t(γ_j−γ_i) (conj z_i · z_j)
  = (Σ_i bfac_i)(Σ_j efac_j) − (Σ_i bfac'_i)(Σ_j efac'_j),
```

with `bfac_i = (γ_i I e^{−iγ_i t}) conj(z_i)`, `efac_j = e^{iγ_j t} z_j`
and the primed pair the conjugate-angle variants — the rank-two
boundary structure that the Lemma-10 Gram identity's correction terms
carry.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8BoundaryBridge

open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open ConnesWeilRH.Source.C1BombieriSection8ExpSum
open scoped ComplexConjugate

variable {n : Nat}

/-- Conjugation commutes with the window exponential and flips the
angle: `conj(e^{ix}) = e^{−ix}` in the canonical single-cast form. -/
theorem conj_expI (x : Real) :
    conj (Complex.exp (Complex.ofReal x * Complex.I))
      = Complex.exp (Complex.ofReal (-x) * Complex.I) := by
  rw [← Complex.exp_conj, conj_mul_d, Complex.conj_ofReal, Complex.conj_I]
  have harg : (Complex.ofReal x * -Complex.I) = Complex.ofReal (-x) * Complex.I := by
    rw [Complex.ofReal_neg]
    ring
  rw [harg]

/-- The Euler half-turn: `−2 sin a = I (e^{ia} − e^{−ia})` in the
canonical single-cast form. -/
theorem negTwoSinI (a : Real) :
    -Complex.ofReal (2 * Real.sin a)
      = Complex.I * (Complex.exp (Complex.ofReal a * Complex.I)
          - Complex.exp (Complex.ofReal (-a) * Complex.I)) := by
  have hE1 := exp_i_mul_real 1 a
  rw [one_mul] at hE1
  rw [← conj_expI a, hE1, map_add (starRingEnd Complex), Complex.conj_ofReal,
    conj_mul_d, Complex.conj_I, Complex.conj_ofReal]
  have hexp : Complex.I * ((Complex.ofReal (Real.cos a)
        + Complex.I * Complex.ofReal (Real.sin a))
      - (Complex.ofReal (Real.cos a) + -Complex.I * Complex.ofReal (Real.sin a)))
    = 2 * (Complex.I * Complex.I) * Complex.ofReal (Real.sin a) := by
    ring
  rw [hexp, Complex.I_mul_I]
  push_cast
  ring

/-- The angle-times-window identity: `θ · winInt t θ = 2 sin(θt)`
(cast into `ℂ`), unifying the diagonal and off-diagonal cases of
`winInt`. -/
theorem mul_winInt_eq_sin (t θ : Real) (ht : 0 ≤ t) :
    Complex.ofReal θ * winInt t θ = Complex.ofReal (2 * Real.sin (θ * t)) := by
  by_cases hθ : θ = 0
  · subst hθ
    rw [winInt, if_pos rfl]
    push_cast
    simp
  · rw [winInt, if_neg hθ]
    have hreal : θ * (2 * Real.sin (θ * t) / θ) = 2 * Real.sin (θ * t) := by
      field_simp
    rw [← Complex.ofReal_mul, hreal]

/-- The even-index boundary factor: `(γ_i I e^{−iγ_i t}) conj(z_i)`. -/
private noncomputable def bfac (t : Real) (γ : Fin n → Real)
    (z : Fin n → Complex) (i : Fin n) : Complex :=
  (Complex.ofReal (γ i) * Complex.I
    * Complex.exp (Complex.ofReal (-(γ i * t)) * Complex.I)) * conj (z i)

/-- The odd-index boundary factor: `(γ_i I e^{iγ_i t}) conj(z_i)`. -/
private noncomputable def bfac' (t : Real) (γ : Fin n → Real)
    (z : Fin n → Complex) (i : Fin n) : Complex :=
  (Complex.ofReal (γ i) * Complex.I
    * Complex.exp (Complex.ofReal (γ i * t) * Complex.I)) * conj (z i)

/-- The boundary exponential at the positive angle: `e^{iγ_j t} z_j`. -/
private noncomputable def efac (t : Real) (γ : Fin n → Real)
    (z : Fin n → Complex) (j : Fin n) : Complex :=
  Complex.exp (Complex.ofReal (γ j * t) * Complex.I) * z j

/-- The boundary exponential at the negative angle: `e^{−iγ_j t} z_j`. -/
private noncomputable def efac' (t : Real) (γ : Fin n → Real)
    (z : Fin n → Complex) (j : Fin n) : Complex :=
  Complex.exp (Complex.ofReal (-(γ j * t)) * Complex.I) * z j

/-- The per-pair bridge: the weighted window pair collapses to the
difference of the boundary-factor products, through
`θ · winInt = 2 sin(θt)`, the Euler half-turn, and the angle split
`e^{i(γ_j−γ_i)t} = e^{iγ_j t} conj(e^{iγ_i t})`. -/
theorem boundaryPair (t : Real) (ht : 0 ≤ t)
    (γ : Fin n → Real) (z : Fin n → Complex) (i j : Fin n) :
    (Complex.ofReal (γ i) * Complex.ofReal (γ i - γ j))
        * winInt t (γ j - γ i) * (conj (z i) * z j)
      = bfac t γ z i * efac t γ z j - bfac' t γ z i * efac' t γ z j := by
  have hflip : (γ i - γ j : Real) = -(γ j - γ i) := by ring
  have hB1 : Complex.ofReal (γ i - γ j) * winInt t (γ j - γ i)
      = -Complex.ofReal (2 * Real.sin ((γ j - γ i) * t)) := by
    rw [hflip, Complex.ofReal_neg, neg_mul, mul_winInt_eq_sin t (γ j - γ i) ht]
  have hE : Complex.exp (Complex.ofReal ((γ j - γ i) * t) * Complex.I)
      = Complex.exp (Complex.ofReal (γ j * t) * Complex.I)
        * Complex.exp (Complex.ofReal (-(γ i * t)) * Complex.I) := by
    rw [← Complex.exp_add]
    have h1 : ((γ j - γ i) * t : Real) = γ j * t + -(γ i * t) := by ring
    rw [h1, Complex.ofReal_add, add_mul]
  have hE2 : Complex.exp (Complex.ofReal (-((γ j - γ i) * t)) * Complex.I)
      = Complex.exp (Complex.ofReal (-(γ j * t)) * Complex.I)
        * Complex.exp (Complex.ofReal (γ i * t) * Complex.I) := by
    rw [← Complex.exp_add]
    have h1 : (-((γ j - γ i) * t) : Real) = -(γ j * t) + γ i * t := by ring
    rw [h1, Complex.ofReal_add, add_mul]
  unfold bfac bfac' efac efac'
  rw [mul_assoc (Complex.ofReal (γ i)) (Complex.ofReal (γ i - γ j))
    (winInt t (γ j - γ i)), hB1, negTwoSinI ((γ j - γ i) * t), hE, hE2]
  ring

/-- FLAGSHIP (slice 12b): the boundary bridge — the weighted double
sum whose diagonal-sinc weight is `γ_i (γ_i − γ_j)` factors completely
into boundary products:

```
ΣΣ γ_i(γ_i−γ_j) winInt t(γ_j−γ_i) (conj z_i z_j)
  = (Σ_i bfac_i)(Σ_j efac_j) − (Σ_i bfac'_i)(Σ_j efac'_j),
```

the rank-two structure carried by the Lemma-10 Gram identity's
correction terms.  DETECTOR only. -/
theorem gamma_sin_boundaryBridge (t : Real) (ht : 0 ≤ t)
    (γ : Fin n → Real) (z : Fin n → Complex) :
    (∑ i, ∑ j, (Complex.ofReal (γ i) * Complex.ofReal (γ i - γ j))
        * winInt t (γ j - γ i) * (conj (z i) * z j))
      = (∑ i, bfac t γ z i) * (∑ j, efac t γ z j)
        - (∑ i, bfac' t γ z i) * (∑ j, efac' t γ z j) := by
  simp only [boundaryPair t ht γ z, Finset.sum_sub_distrib]
  have hprod1 : (∑ i : Fin n, ∑ j : Fin n, bfac t γ z i * efac t γ z j)
      = (∑ i : Fin n, bfac t γ z i) * (∑ j : Fin n, efac t γ z j) :=
    (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i : Fin n => bfac t γ z i)
      (g := fun j : Fin n => efac t γ z j)).symm
  have hprod2 : (∑ i : Fin n, ∑ j : Fin n, bfac' t γ z i * efac' t γ z j)
      = (∑ i : Fin n, bfac' t γ z i) * (∑ j : Fin n, efac' t γ z j) :=
    (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i : Fin n => bfac' t γ z i)
      (g := fun j : Fin n => efac' t γ z j)).symm
  rw [hprod1, hprod2]

end C1BombieriSection8BoundaryBridge
end Source
end ConnesWeilRH
