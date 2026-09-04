/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1WindowRationalIngest

/-!
# Record 1119: generic entrywise bounds + quadratic-form symmetrization

The two generic lemmas of the T-box (Gt, Mt)-level pull-through
(docs/proofs/1119_hbox_tbox_pullthrough_preregistration.md section 1b):

- the quadratic form of a real matrix only sees its symmetrization, so the
  certificate chain may symmetrize the perturbation losslessly;
- an entrywise bound on the factors `X`, `B`, `Y` gives the matching
  entrywise bound on the triple product `Xᵀ * B * Y` - the propagation
  step that pushes the (|U| radG + radM) box through `K` and `Lam`.

RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1EntrywiseBound

open Matrix
open C1WindowRationalIngest

/-- The quadratic form of a real matrix equals the quadratic form of its
symmetrization `(M + Mᵀ)/2` (the skew-symmetric part drops out). -/
theorem qform_sym_half {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (M.mulVec x) = x ⬝ᵥ (((1 : ℝ) / 2) • (M + M.transpose)).mulVec x := by
  rw [Matrix.smul_mulVec, dotProduct_smul]
  have h2 : x ⬝ᵥ ((M + M.transpose).mulVec x) = 2 * x ⬝ᵥ (M.mulVec x) := by
    rw [Matrix.add_mulVec, dotProduct_add, qf_transpose M x, two_mul]
  rw [h2]
  ring

/-- Entrywise triangle bound through a triple product: entrywise bounds
`|X| ≤ xb`, `|B| ≤ bb`, `|Y| ≤ yb` give the matching entrywise bound
`|Xᵀ * B * Y| ≤ xbᵀ * bb * yb`. -/
theorem entrywise_triple {r c : ℕ}
    (X Y : Matrix (Fin r) (Fin c) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (xb yb : Matrix (Fin r) (Fin c) ℝ) (bb : Matrix (Fin r) (Fin r) ℝ)
    (hx : ∀ i j, |X i j| ≤ xb i j) (hb : ∀ i j, |B i j| ≤ bb i j)
    (hy : ∀ i j, |Y i j| ≤ yb i j) (k l : Fin c) :
    |((Matrix.transpose X * B) * Y) k l| ≤ (Matrix.transpose xb * bb * yb) k l := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  refine le_trans (abs_sum_le_sum_abs (s := Finset.univ) (f := fun i =>
    Finset.univ.sum fun j => X i k * (B i j * Y j l))) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_trans (abs_sum_le_sum_abs (s := Finset.univ) (f := fun j =>
    X i k * (B i j * Y j l))) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |X i k| ≤ xb i k := hx i k
  have h2 : |B i j| ≤ bb i j := hb i j
  have h3 : |Y j l| ≤ yb j l := hy j l
  nlinarith [abs_nonneg (X i k), abs_nonneg (B i j), abs_nonneg (Y j l)]

end C1EntrywiseBound
end Source
end ConnesWeilRH
