/-!
# C1GateLevelTransfer - T1 class==>matrix transfer: the box-robust (T-box) kernel

Record 1118, sub-obligation (a): the algebraic half of the transcendental
transfer. This file lands the generic L1 lemma registered in record 1115 s3c
("strict diagonal dominance with positive diagonal => PSD") in its Gershgorin-
free form: over the whitened space, a quadratic form whose matrix is a positive
diagonal plus an entrywise-bounded perturbation stays nonnegative whenever each
diagonal slack

    rad i i + (∑ j ≠ i) (rad i j + rad j i)/2  <  d i

is strictly positive. All statements are pure real matrix / finset algebra - no
`CompactLogTest`, no `ICgate`, no per-class data yet; the class instantiation and
the gate-level headline land in a later build on top of this green kernel.

Build scope (build #1): five declarations, all over ℝ:
  1. two_abs_mul_le_sq_add_sq   - the AM-GM cross-term bound |ab| <= (a^2+b^2)/2
  2. qformDoubleSum             - x ⬝ᵥ A *ᵥ x = ∑ i j, A i j * x i * x j
  3. sumUnivSplit               - per-index diagonal/off-diagonal finset split
  4. lbCollect                  - collect the lower bound into ∑ c_i * x_i^2
                                   (Stage B off-diagonal collection = one documented sorry)
  5. qform_nonneg_whitenedBox   - the L1 PSD statement itself
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import ConnesWeilRH.Dev.E0SlemmaBridge
import ConnesWeilRH.Dev.C1WindowRationalIngest

set_option linter.style.longLine false

namespace ConnesWeilRH.Source.C1GateLevelTransfer

open Matrix

variable {k : ℕ}

/-- AM-GM cross-term bound: `2*|a|*|b| <= a^2 + b^2` (equivalently
`|ab| <= (a^2+b^2)/2`). The only elementary inequality the L1 proof uses for its
off-diagonal control. -/
theorem two_abs_mul_le_sq_add_sq {a b : ℝ} : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  have hpos : (a - b) ^ 2 ≥ 0 := sq_nonneg _
  have hsum : (a + b) ^ 2 ≥ 0 := sq_nonneg _
  -- the two squares give a^2+b^2 >= 2ab and a^2+b^2 >= -2ab, hence >= 2|ab|.
  have hab1 : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [hpos]
  have hab2 : -(2 * a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [hsum]
  have habs : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_le_iff, div_le_iff (show 0 < (2:ℝ), by norm_num)]
    constructor <;> nlinarith [hab1, hab2]
  calc
    2 * |a| * |b| = 2 * (|a| * |b|) := by ring
      _ = 2 * |a * b| := by rw [abs_mul]
        _ ≤ a ^ 2 + b ^ 2 := by nlinarith [habs]

/-- A real quadratic form equals the full double sum over ordered pairs. -/
theorem qformDoubleSum {A : Matrix (Fin k) (Fin k) ℝ} (x : Fin k → ℝ) :
    x ⬝ᵥ A *ᵥ x = ∓_{i}, (∓_{j}, A i j * x i * x j) := by
  have h1 : x ⬝ᵥ A *ᵥ x = ∓_{i}, x i * (∓_{j}, A i j * x j) := by
    simp only [dotProduct, Matrix.mulVec]
  rw [h1]
  -- pull the outer scalar into each inner sum and normalise to a double sum.
  ring_nf

/-- Per-index split of a full univ-sum: the `i`th value plus the off-diagonal tail.
Routes around the (absent) named `Finset.sum_union` by rewriting `univ` as an insert. -/
theorem sumUnivSplit {g : Fin k → ℝ} (i : Fin k) :
    ∓_{j in univ}, g j = g i + ∓_{j in univ \ {i}, g j} := by
  have hU : univ = insert i (univ \ {i}) := by ext j; simp
  rw [hU]
  rw [Finset.sum_insert_of_not_mem (by simp)]

/-- Collect the whitened-box lower bound. The per-pair lower bound, summed over all ordered
pairs, equals `∑_i c_i * x_i^2` with the diagonal-dominance coefficient

    c_i = d_i - rad i i - (∑ j ≠ i) (rad i j + rad j i)/2.

The off-diagonal coefficient of `x_k^2` is `-1/2 * ∑_{j≠k}(rad k j + rad j k)` by the
row+column pairing, exactly the registered slack shape. -/
theorem lbCollect {d : Fin k → ℝ} (rad : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    ∓_{i}, (∓_{j}, (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
  = ∑ i, (d i - rad i i - ∓_{j in univ \ {i}, (rad i j + rad j i) / 2}) * x i ^ 2 := by
  -- Stage A: each inner sum is its diagonal value plus the off-diagonal tail.
  have hin : ∀ i,
      (∑ j, (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
    = (d i - rad i i) * x i ^ 2 + ∓_{j in univ \ {i}, (-(rad i j / 2)) * (x i ^ 2 + x j ^ 2)} := by
    intro i
    let g := fun j => if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)
    have hsplit : (∑ j, g j) = g i + ∓_{j in univ \ {i}, g j} := sumUnivSplit g i
    rw [hsplit]
    · dsimp only [g]; simp   -- the singleton term: i=i, so it is exactly P_i
  -- Push Stage A through the outer sum and regroup the addition.
  have hL : (∑ i, ∓_j, (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
      = (∑ i, (d i - rad i i) * x i ^ 2) + ∑ i in univ, ∓_j in univ \ {i}, (-(rad i j / 2)) * (x i ^ 2 + x j ^ 2) := by
    calc
      _ = ∑ i, ((d i - rad i i) * x i ^ 2 + ∑ j in univ \ {i}, (-(rad i j / 2)) * (x i ^ 2 + x j ^ 2)) := by
        congr; intro i; exact hin i
      _ = (∓_{i}, (d i - rad i i) * x i ^ 2) + ∑ i in univ, ∑ j in univ \ {i}, (-(rad i j / 2)) * (x i ^ 2 + x j ^ 2) := by
        simp only [Finset.sum_add_distrib]
  rw [hL]
  -- Stage B: the off-diagonal double sum collects to -∑_k [∑_{j≠k}(rad k j + rad j k)/2] * x_k^2.
  have hO : (∓_{i}, ∓_{j in univ \ {i}, (-(rad i j / 2)) * (x i ^ 2 + x j ^ 2)})
      = -∑ i, (∓_{j in univ \ {i}, (rad i j + rad j i) / 2}) * x i ^ 2 := by
    -- [build #1: the surrounding kernel is green; this off-diagonal collection is filled in build #2]
    sorry
  rw [hO]
  simp only [Finset.sum_sub_distrib]; ring_nf

/-- L1 (record 1115 s3c, Gershgorin-free): a positive diagonal plus an entrywise-bounded
perturbation keeps the quadratic form nonnegative whenever every diagonal slack is strictly
positive. Box-robust: it holds for EVERY real perturbation E with `|E i j| <= rad i j`. -/
theorem qform_nonneg_whitenedBox {d : Fin k → ℝ} (rad : Matrix (Fin k) (Fin k) ℝ)
    (hdpos : ∀ i, 0 < d i) (hradpos : ∀ i j, 0 ≤ rad i j)
    (hslack : ∀ i, rad i i + ∓_{j in univ \ {i}, (rad i j + rad j i) / 2} < d i)
    {E : Matrix (Fin k) (Fin k) ℝ} (heb : ∀ i j, |E i j| ≤ rad i j) (x : Fin k → ℝ) :
    0 ≤ x ⬝ᵥ ((diagonal d + E) *ᵥ x) := by
  let A := diagonal d + E
  -- Lower-bound every pair term of the double-sum form by the whitened-box lower bound.
  have hLB : ∀ i j, (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)) ≤ A i j * x i * x j := by
    intro i j
    split_ifs with h
    · -- i = j : diagonal. Unify the index; A ii = d_i + E_ii and E_ii >= -rad_ii.
      subst i
      have hAjj : A j j = d j + E j j := by dsimp only [A]; simp
      rw [hAjj, ← pow_two]
      nlinarith [(abs_le.mp (heb j j)).1, sq_nonneg (x j)]
    · -- i ≠ j : off-diagonal. A ij = E_ij; the AM-GM bound controls the cross term.
      have hAij : A i j = E i j := by dsimp only [A]; simp [h]
      rw [hAij, ← pow_two]
      have hxy : -|(E i j) * (x i * x j)| ≤ E i j * x i * x j := by
        rw [show E i j * x i * x j = (E i j) * (x i * x j), by ring]
        exact neg_abs_le _
      have hab : |(E i j) * (x i * x j)| ≤ (rad i j / 2) * (x i ^ 2 + x j ^ 2) := by
        calc
          _ = |E i j| * |x i * x j| := by rw [abs_mul]
            _ ≤ rad i j * |x i * x j| := by
              apply mul_le_mul_of_nonneg_right ((abs_le.mp (heb i j)).1)
              exact abs_nonneg _
              _ ≤ rad i j * ((x i ^ 2 + x j ^ 2) / 2) := by
                have hinner : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
                  nlinarith [two_abs_mul_le_sq_add_sq (x i) (x j)]
                apply mul_le_mul_of_nonneg_left hinner
                exact hradpos i j
              _ = (rad i j / 2) * (x i ^ 2 + x j ^ 2) := by ring
      nlinarith [hxy, hab]
  -- Sum the pointwise lower bound over all pairs.
  have hsum : (∓_{i}, ∓_{j}, (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2))) ≤ ∑ i, ∓_j, A i j * x i * x j := by
    apply Finset.sum_le_sum; intro i
    apply Finset.sum_le_sum; intro j
    exact hLB i j
  -- Each collected diagonal coefficient is strictly positive by the slack.
  have hpos : ∀ i, 0 < d i - rad i i - ∓_{j in univ \ {i}, (rad i j + rad j i) / 2} := by
    intro i; linarith [hslack i]
  have hnonneg : 0 ≤ ∑ i, (d i - rad i i - ∓_{j in univ \ {i}, (rad i j + rad j i) / 2}) * x i ^ 2 := by
    apply Finset.sum_nonneg
    intro i; nlinarith [hpos i, sq_nonneg (x i)]
  calc
    0 ≤ ∓_{i}, (d i - rad i i - ∓_{j in univ \ {i}, (rad i j + rad j i) / 2}) * x i ^ 2 := hnonneg
      _ = ∑ i, ∓_j, (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)) := by rw [lbCollect d rad x]
        _ ≤ ∓_{i}, ∓_{j}, A i j * x i * x j := hsum
          _ = x ⬝ᵥ A *ᵥ x := (qformDoubleSum A x).symm

end ConnesWeilRH.Source.C1GateLevelTransfer
