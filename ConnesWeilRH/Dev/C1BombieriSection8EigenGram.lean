/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Gamma
import ConnesWeilRH.Dev.C1BombieriSection8ExpMass

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, fourteenth slice: the eigen-relation Gram transport

First half of the eigen-relation assembly of the (8.11) readback
(Bombieri's Lemma 10, book pp.209-212): from the (7.4) eigenvalue
equation for the weighted vector

```
w = bombieriWOfZ γ z,      w = Λ • H(Γ;t) *ᵥ w,
```

derive the Gram-quadratic identity obtained by multiplying the
eigen-equation by `conj(w_i)` and summing over the finite Γ:

```
Σ_i w_i conj(w_i)  =  Λ · Σ_i Σ_j 2t K*(γ_i,γ_j;t) z_j conj(w_i),
```

with `conj(w_i) = (1/4 + γ_i²) conj(z_i)` — the (7.2) weight on the
conjugate side, the raw `K*`-matrix on the data side.  This is the
matrix-side transport that the Lemma-10 substitution (sinc channel →
Q-form + rank-two boundary products) consumes; the fold against
`wirtingerFull` is the next slice.  Stated with `Λ` directly (no
division), so no nonvanishing premise on the eigenvalue is needed.
DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8EigenGram

open ConnesWeilRH.Source.C1BombieriSection7Gamma
open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open scoped ComplexConjugate

variable {n : Nat}

/-- Conjugation of the (7.2) weight: `conj(w_i) = (1/4 + γ_i²) conj(z_i)`
— the real weight passes through, the data coordinate conjugates. -/
theorem conj_bombieriWOfZ (gamma : Fin n → Real) (z : Fin n → Complex)
    (i : Fin n) :
    conj (bombieriWOfZ gamma z i)
      = ((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i) := by
  unfold bombieriWOfZ
  rw [conj_mul_d, Complex.conj_ofReal]

/-- The raw `K*`-matrix readback of the weighted mulVec: entry `i` is the
finite sum `∑ j, 2t K*(γ_i,γ_j;t) z_j` (the (6.4) right-hand side). -/
theorem mulVec_weight_apply (gamma : Fin n → Real) (t : Real)
    (z : Fin n → Complex) (i : Fin n) :
    (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z) i
      = ∑ j, ((2 * t : Real) : Complex) * bombieriKstar (gamma i) (gamma j) t
          * z j := by
  rw [bombieriHMatrix_mulVec_weight]
  rfl

/-- FLAGSHIP (slice 12c): the eigen-relation Gram transport — the (7.4)
eigen-equation multiplied by `conj(w_i)` and summed over the finite Γ:

```
Σ_i w_i conj(w_i) = Λ · Σ_i Σ_j 2t K*(γ_i,γ_j;t) z_j conj(w_i),
```

with `conj(w_i) = (1/4 + γ_i²) conj(z_i)`.  The first slot of the
eigen-equation is transported by `congrArg` (an `rw` would rewrite the
`w_i` inside the conjugation as well), the mulVec through the raw
`K*`-matrix readback, and `Λ` is pulled out of the double sum by
`Finset.mul_sum`.  DETECTOR only. -/
theorem bombieriEigen_gram (t : Real) (gamma : Fin n → Real)
    (z : Fin n → Complex) (Lam : Complex)
    (h : bombieriWOfZ gamma z
        = Lam • (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)) :
    (∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i))
      = Lam * ∑ i, ∑ j, ((2 * t : Real) : Complex)
          * bombieriKstar (gamma i) (gamma j) t * z j
          * (((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i)) := by
  have hpc := (bombieriEigenvec_iff gamma t Lam (bombieriWOfZ gamma z)).mp h
  have hsum : ∀ i : Fin n,
      bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i)
      = Lam * ∑ j, ((2 * t : Real) : Complex)
          * bombieriKstar (gamma i) (gamma j) t * z j
          * (((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i)) := by
    intro i
    have h1 : bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i)
        = (Lam * ((bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z) i))
          * conj (bombieriWOfZ gamma z i) :=
      congrArg (fun c : Complex => c * conj (bombieriWOfZ gamma z i)) (hpc i)
    rw [h1, mulVec_weight_apply, conj_bombieriWOfZ, mul_assoc, Finset.sum_mul]
  calc (∑ i, bombieriWOfZ gamma z i * conj (bombieriWOfZ gamma z i))
      = ∑ i, Lam * ∑ j, ((2 * t : Real) : Complex)
          * bombieriKstar (gamma i) (gamma j) t * z j
          * (((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i)) :=
        Finset.sum_congr rfl fun i _ => hsum i
    _ = Lam * ∑ i, ∑ j, ((2 * t : Real) : Complex)
          * bombieriKstar (gamma i) (gamma j) t * z j
          * (((1 / 4 + gamma i ^ 2 : Real) : Complex) * conj (z i)) := by
        rw [← Finset.mul_sum]

end C1BombieriSection8EigenGram
end Source
end ConnesWeilRH
