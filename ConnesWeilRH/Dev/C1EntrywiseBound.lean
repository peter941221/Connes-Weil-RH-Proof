/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1WindowRationalIngest

/-!
# Record 1119: generic entrywise bounds + quadratic-form symmetrization

The generic lemmas of the T-box (Gt, Mt)-level pull-through
(docs/proofs/1119_hbox_tbox_pullthrough_preregistration.md section 1b):

- the quadratic form of a real matrix only sees its symmetrization, so the
  certificate chain may symmetrize the perturbation losslessly;
- an entrywise bound on the factors of a product gives the matching
  entrywise bound on the product (`entrywise_mul`), composed twice to the
  triple product `Xᵀ * B * Y` - the propagation step that pushes the
  `(mu radG + radM)` box through `K` and `Lam`.

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

/-- Entrywise triangle bound through a product: entrywise bounds
`|A| ≤ ab`, `|B| ≤ p` give the matching entrywise bound on `A * B`. -/
theorem entrywise_mul {r s t : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (B : Matrix (Fin s) (Fin t) ℝ)
    (ab : Matrix (Fin r) (Fin s) ℝ) (p : Matrix (Fin s) (Fin t) ℝ)
    (ha : ∀ i j, |A i j| ≤ ab i j) (hb : ∀ i j, |B i j| ≤ p i j)
    (k : Fin r) (l : Fin t) :
    |(A * B) k l| ≤ (ab * p) k l := by
  rw [Matrix.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs (f := fun i => A k i * B i l)
    (s := Finset.univ)) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  nlinarith [ha k i, hb i l, abs_nonneg (A k i), abs_nonneg (B i l)]

/-- Entrywise triangle bound through a triple product: entrywise bounds
`|X| ≤ xb`, `|B| ≤ bb`, `|Y| ≤ yb` give the matching entrywise bound
`|Xᵀ * B * Y| ≤ xbᵀ * bb * yb`. -/
theorem entrywise_triple {r c : ℕ}
    (X Y : Matrix (Fin r) (Fin c) ℝ) (B : Matrix (Fin r) (Fin r) ℝ)
    (xb yb : Matrix (Fin r) (Fin c) ℝ) (bb : Matrix (Fin r) (Fin r) ℝ)
    (hx : ∀ i j, |X i j| ≤ xb i j) (hb : ∀ i j, |B i j| ≤ bb i j)
    (hy : ∀ i j, |Y i j| ≤ yb i j) (k l : Fin c) :
    |((Matrix.transpose X * B) * Y) k l| ≤ (Matrix.transpose xb * bb * yb) k l := by
  have hxt : ∀ i j, |(Matrix.transpose X) i j| ≤ (Matrix.transpose xb) i j := by
    intro i j
    simpa [Matrix.transpose_apply] using hx j i
  have h1 : ∀ i j, |(Matrix.transpose X * B) i j| ≤ (Matrix.transpose xb * bb) i j :=
    fun i j => entrywise_mul (Matrix.transpose X) B (Matrix.transpose xb) bb hxt hb i j
  exact entrywise_mul (Matrix.transpose X * B) Y (Matrix.transpose xb * bb) yb h1 hy k l

end C1EntrywiseBound
end Source
end ConnesWeilRH
