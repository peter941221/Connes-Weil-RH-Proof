/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7H

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The finite-Γ ownership layer: (7.2), (7.4), (7.5)

Section 7 of Bombieri's memoir (book p.203, design record
`docs/proofs/1043` sections 6y/6z) investigates the linear system (6.4)
after the change of variables `ρ = 1/2 + iγ`, `M = e^t`, `Λ = 1/λ`.  With

```
(7.2)  z_γ = X_ρ,   w_γ = (1/4 + γ^2) z_γ,   Λ = 1/λ
(7.3)  H(x,y,t) = 2 t K*(x,y,t) / (1/4 + y^2)
```

the eigenvalue equation becomes

```
(7.4)  w_γ = Λ Σ_{γ'} H(γ,γ',t) w_{γ'}
```

where `Λ` is the SCALAR `1/λ`, and the resolvent determinant is

```
(7.5)  D(Λ,t) = det[I − Λ H(Γ;t)],   H(Γ;t) = [H(γ,γ',t)]_{γ,γ'∈Γ}.
```

This leaf models a finite zero multiset Γ as an arbitrary map
`gamma : Fin n → Real` (repetitions carry the multiplicity `m(γ)`), and
lands:

* `bombieriWOfZ` — the (7.2) coordinate change `w_γ = (1/4 + γ^2) z_γ`;
* `bombieriHMatrix` — the matrix `H(Γ;t)`;
* `bombieriHMatrix_transpose` — `H(Γ;t)` is symmetric (the flagship
  `bombieriH_symmetric` off the diagonal, trivially on it);
* `bombieriHMatrix_mulVec_weight` — the ownership identity: the `H`-matrix
  acting on the weighted vector `(1/4 + γ^2) z` is twice `t` times the raw
  `K*`-matrix acting on `z`, so (7.4) is exactly the original system (6.4);
* `bombieriEigenvec_iff` — the (7.4) eigenvalue equation in matrix-vector
  form `w = Λ • H(Γ;t) *ᵥ w` iff per component;
* `bombieriD` — the (7.5) resolvent determinant, with `D(0,t) = 1`
  (the constant term of Bombieri's Theorem 6).

The coefficient `X_ρ` itself is the section-6 expansion coefficient of
(6.1) (`f(x) = Σ_ρ X_ρ φ(x) x^{-ρ} + X_0 φ(x) + X_1 φ(x) x^{-1}` on
`(M^{-1}, M)` with `φ` the characteristic function of `(1/M, M)`, the
end corrections (6.2) killing `f` at the endpoints); in the finite-certificate
lane the vector `z` enters as explicit data indexed by Γ, so this leaf
needs no function-space infrastructure.  No numerical datum enters any
leaf: only exact identities are proven.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7Gamma

open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection7H

variable {n : ℕ}

/-- The elementwise form of `mulVec` (definitional): entry `i` of
`M *ᵥ v` is the finite sum `∑ j, M i j * v j`. -/
private theorem mulVec_apply_eq (M : Matrix (Fin n) (Fin n) Complex)
    (v : Fin n → Complex) (i : Fin n) :
    M.mulVec v i = ∑ j, M i j * v j := rfl

/-- (7.2): the coordinate change from `z` to `w`, `w_γ = (1/4 + γ^2) z_γ`.
The real weight is strictly positive, so this is a linear change with
nonvanishing diagonal. -/
noncomputable def bombieriWOfZ (gamma : Fin n → Real) (z : Fin n → Complex) :
    Fin n → Complex :=
  fun i => ((1 / 4 + gamma i ^ 2 : Real) : Complex) * z i

/-- The matrix `H(Γ;t)` of (7.4): entry `(i, j)` is the normalized kernel
`H(γ_i, γ_j; t)`. -/
noncomputable def bombieriHMatrix (gamma : Fin n → Real) (t : Real) :
    Matrix (Fin n) (Fin n) Complex :=
  Matrix.of fun i j => bombieriH (gamma i) (gamma j) t

/-- `H(Γ;t)` is symmetric: off the diagonal by `bombieriH_symmetric`, on
the diagonal trivially. -/
theorem bombieriHMatrix_transpose (gamma : Fin n → Real) (t : Real) (ht : t ≠ 0) :
    Matrix.transpose (bombieriHMatrix gamma t) = bombieriHMatrix gamma t := by
  ext i j
  simp only [Matrix.transpose_apply, bombieriHMatrix, Matrix.of_apply]
  by_cases hEq : gamma i = gamma j
  · rw [hEq]
  · rw [bombieriH_symmetric (gamma j) (gamma i) t ht (Ne.symm hEq)]

/-- The per-entry ownership identity: the weight factors out of `H` and
leaves `2 t K*`.  Stated in the left-associated shape that `simp` gives
the summands, so the `mulVec` proof needs no reassociation. -/
private theorem entry_eq (x y t : Real) (z : Complex) :
    bombieriH x y t * (((1 / 4 + y ^ 2 : Real) : Complex) * z)
      = ((2 * t : Real) : Complex) * bombieriKstar x y t * z := by
  rw [← mul_assoc (bombieriH x y t) ((1 / 4 + y ^ 2 : Real) : Complex) z,
    mul_comm (bombieriH x y t) ((1 / 4 + y ^ 2 : Real) : Complex),
    bombieriH_mul_weight_eq x y t]

/-- The ownership identity joining (7.2) and (7.3): the `H`-matrix acting
on the weighted vector `w = (1/4 + γ^2) z` is twice `t` times the raw
`K*`-matrix acting on `z`.  This is why (7.4) is equivalent to the
original eigenvalue system (6.4). -/
theorem bombieriHMatrix_mulVec_weight (gamma : Fin n → Real) (t : Real)
    (z : Fin n → Complex) :
    (bombieriHMatrix gamma t).mulVec (bombieriWOfZ gamma z)
      = (Matrix.of fun i j => ((2 * t : Real) : Complex)
            * bombieriKstar (gamma i) (gamma j) t).mulVec z := by
  funext i
  rw [mulVec_apply_eq, mulVec_apply_eq]
  simp only [bombieriHMatrix, Matrix.of_apply, bombieriWOfZ]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact entry_eq (gamma i) (gamma j) t (z j)

/-- (7.4): the eigenvalue equation `w_γ = Λ Σ_{γ'} H(γ,γ',t) w_{γ'}`,
stated as the matrix-vector form `w = Λ • H(Γ;t) *ᵥ w` iff the per
component form. -/
theorem bombieriEigenvec_iff (gamma : Fin n → Real) (t : Real)
    (Lam : Complex) (w : Fin n → Complex) :
    w = Lam • (bombieriHMatrix gamma t).mulVec w
      ↔ ∀ i, w i = Lam * ((bombieriHMatrix gamma t).mulVec w i) := by
  constructor
  · -- `congrArg`, not `rw`: `h` mentions `w` on both sides, so `rw [h]`
    -- would also rewrite the `w` inside `mulVec w`.
    intro h i
    have hi : w i = (Lam • (bombieriHMatrix gamma t).mulVec w) i :=
      congrArg (fun v : Fin n → Complex => v i) h
    rw [Pi.smul_apply, smul_eq_mul] at hi
    exact hi
  · intro h
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact h i

/-- (7.5): the resolvent determinant `D(Λ,t) = det[I − Λ H(Γ;t)]`.
Here `Λ` is the scalar `1/λ`, exactly as in the book. -/
noncomputable def bombieriD (gamma : Fin n → Real) (Lam : Complex) (t : Real) :
    Complex :=
  Matrix.det (1 - Lam • bombieriHMatrix gamma t)

/-- The constant term of Bombieri's Theorem 6: `D(0,t) = 1`. -/
theorem bombieriD_zero (gamma : Fin n → Real) (t : Real) :
    bombieriD gamma 0 t = 1 := by
  unfold bombieriD
  rw [zero_smul, sub_zero]
  exact Matrix.det_one

end C1BombieriSection7Gamma
end Source
end ConnesWeilRH
