/-
# C1GateLevelTransfer - T1 class==>matrix transfer: the box-robust (T-box) kernel

Record 1118, sub-obligation (a): the algebraic half of the transcendental
transfer. This file lands the generic L1 lemma registered in record 1115 s3c
("strict diagonal dominance with positive diagonal => PSD") in its Gershgorin-
free form: over the whitened space, a quadratic form whose matrix is a positive
diagonal plus an entrywise-bounded perturbation stays nonnegative whenever each
diagonal slack

    rad i i + (sum j != i) (rad i j + rad j i)/2  <  d i

is strictly positive. All statements are pure real matrix / finset algebra - no
`CompactLogTest`, no `ICgate`, no per-class data yet; the class instantiation and
the gate-level headline land in a later build on top of this green kernel.

All finset sums are written as explicit ASCII `Finset.sum` (via the `uK`
abbreviation for the full index set) to avoid any BigOperators-glyph ambiguity.

Build scope (build #1): five declarations, all over R:
  1. two_abs_mul_le_sq_add_sq   - the AM-GM cross-term bound |ab| <= (a^2+b^2)/2
  2. qformDoubleSum             - x dot (A *v x) = full double sum
  3. sumUnivSplit               - per-index diagonal/off-diagonal finset split
  4. lbCollect                  - collect the lower bound into sum c_i * x_i^2
                                   (Stage B off-diagonal collection proved in full)
  5. qform_nonneg_whitenedBox   - the L1 PSD statement itself
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import ConnesWeilRH.Dev.E0SlemmaBridge
import ConnesWeilRH.Dev.C1WindowRationalIngest

set_option linter.style.longLine false

namespace ConnesWeilRH.Source.C1GateLevelTransfer

open Matrix

variable {k : ℕ}

-- The full index set of the whitened space; kept as an abbreviation so finset
-- sums stay ASCII and readable throughout this module.
private abbrev uK : Finset (Fin k) := Finset.univ

/-- AM-GM cross-term bound: `2*|a|*|b| <= a^2 + b^2` (equivalently
`|ab| <= (a^2+b^2)/2`). The only elementary inequality the L1 proof uses for its
off-diagonal control. -/
theorem two_abs_mul_le_sq_add_sq (a b : ℝ) : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  have hpos : (a - b) ^ 2 ≥ 0 := sq_nonneg _
  have hsum : (a + b) ^ 2 ≥ 0 := sq_nonneg _
  -- the two squares give a^2+b^2 >= 2ab and a^2+b^2 >= -2ab, hence >= 2|ab|.
  have hab1 : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [hpos]
  have hab2 : -(2 * a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [hsum]
  have habs : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hab1, hab2]
  calc
    2 * |a| * |b| = 2 * (|a| * |b|) := by ring
      _ = 2 * |a * b| := by rw [abs_mul]
        _ ≤ a ^ 2 + b ^ 2 := by nlinarith [habs]

/-- A real quadratic form equals the full double sum over ordered pairs. -/
theorem qformDoubleSum {A : Matrix (Fin k) (Fin k) ℝ} (x : Fin k → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = uK.sum fun i => uK.sum fun j => A i j * x i * x j := by
  have h1 : x ⬝ᵥ (A *ᵥ x) = uK.sum fun i => x i * (uK.sum fun j => A i j * x j) := by
    simp only [dotProduct, Matrix.mulVec]
  rw [h1]
  -- distribute the outer scalar into each inner sum and reorder factors.
  have h2 : (uK.sum fun i => x i * (uK.sum fun j => A i j * x j)) =
      (uK.sum fun i => uK.sum fun j => x i * A i j * x j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h2]
  have h3 : (uK.sum fun i => uK.sum fun j => x i * A i j * x j) =
      (uK.sum fun i => uK.sum fun j => A i j * x i * x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h3]

/-- Per-index split of a full univ-sum: the `i`th value plus the off-diagonal tail.
Rewrites `univ` as `insert i (univ \ {i})` so `Finset.sum_insert` applies directly. -/
theorem sumUnivSplit {g : Fin k → ℝ} (i : Fin k) :
    uK.sum g = g i + (uK \ {i}).sum g := by
  have hu : uK = insert i (uK \ {i}) := by ext j; simp
  conv_lhs => rw [hu]
  rw [Finset.sum_insert (by simp : i ∉ uK \ {i})]

/-- Collect the whitened-box lower bound. The per-pair lower bound, summed over all ordered
pairs, equals `sum_i c_i * x_i^2` with the diagonal-dominance coefficient

    c_i = d_i - rad i i - (sum j != i) (rad i j + rad j i)/2.

The off-diagonal coefficient of `x_k^2` is `-1/2 * sum_{j!=k}(rad k j + rad j k)` by the
row+column pairing, exactly the registered slack shape. -/
theorem lbCollect {d : Fin k → ℝ} (rad : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    (uK.sum fun i => uK.sum fun j => (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
  = (uK.sum fun i => (d i - rad i i - (uK \ {i}).sum fun j => (rad i j + rad j i) / 2) * x i ^ 2) := by
  -- Stage A: each inner sum is its diagonal value plus the off-diagonal tail.
  have hin : ∀ i : Fin k, uK.sum (fun j => (if i = j then (d i - rad i i) * x i ^ 2
        else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
      = (d i - rad i i) * x i ^ 2
        + (uK \ {i}).sum (fun j => -(rad i j / 2) * (x i ^ 2 + x j ^ 2)) := by
    intro i
    rw [sumUnivSplit (g := fun j => (if i = j then (d i - rad i i) * x i ^ 2
        else -(rad i j / 2) * (x i ^ 2 + x j ^ 2))) i]
    rw [if_pos rfl]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (fun h : i = j =>
      (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mpr h.symm)))]
  -- Push Stage A through the outer sum and regroup the addition.
  have hL : (uK.sum fun i => uK.sum fun j => (if i = j then (d i - rad i i) * x i ^ 2
        else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
      = (uK.sum fun i => (d i - rad i i) * x i ^ 2)
        + (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * (x i ^ 2 + x j ^ 2))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hin i)
  rw [hL]
  -- Stage B: the off-diagonal double sum collects to -sum_i [C_i] * x_i^2, where
  -- C_i = (sum_{j != i}) (rad i j + rad j i)/2 by the row+column pairing.
  have hO : (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
      = -(uK.sum fun i => ((uK \ {i}).sum fun j => (rad i j + rad j i) / 2) * x i ^ 2) := by
    -- Rewrite each restricted sum as a full sum with an `if` zeroing the diagonal,
    -- swap the two full sums, and split each summand into its row and column share.
    have hrestrict : ∀ (f : Fin k → ℝ) (i : Fin k),
        (uK \ {i}).sum f = uK.sum (fun j => if j = i then 0 else f j) := by
      intro f i
      rw [sumUnivSplit (g := fun j => if j = i then 0 else f j) i]
      rw [if_pos rfl]
      rw [Finset.sum_congr rfl (fun j hj => if_neg (fun h : j = i =>
        (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mpr h)))]
      rw [zero_add]
    have hswap : ∀ g : Fin k → Fin k → ℝ,
        (uK.sum fun i => (uK \ {i}).sum (fun j => g i j))
          = (uK.sum fun j => (uK \ {j}).sum (fun i => g i j)) := by
      intro g
      have s1 : (uK.sum fun i => (uK \ {i}).sum (fun j => g i j))
          = (uK.sum fun i => uK.sum (fun j => if j = i then 0 else g i j)) :=
        Finset.sum_congr rfl (fun i _ => hrestrict (g i) i)
      have s2 : (uK.sum fun i => uK.sum (fun j => if j = i then 0 else g i j))
          = (uK.sum fun j => uK.sum (fun i => if j = i then 0 else g i j)) :=
        Finset.sum_comm
      have s3 : (uK.sum fun j => uK.sum (fun i => if j = i then 0 else g i j))
          = (uK.sum fun j => (uK \ {j}).sum (fun i => g i j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sumUnivSplit (g := fun i => if j = i then 0 else g i j) j]
        rw [if_pos rfl]
        rw [Finset.sum_congr rfl (fun i hi => if_neg (fun h : j = i =>
          (Finset.mem_sdiff.mp hi).2 (Finset.mem_singleton.mpr h.symm)))]
        rw [zero_add]
      rw [s1, s2, s3]
    have hA : (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * x i ^ 2))
        = (uK.sum fun i => ((uK \ {i}).sum (fun j => -(rad i j / 2))) * x i ^ 2) :=
      Finset.sum_congr rfl (fun i _ => (Finset.sum_mul _ _ _).symm)
    have hB : (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * x j ^ 2))
        = (uK.sum fun j => ((uK \ {j}).sum (fun i => -(rad i j / 2))) * x j ^ 2) := by
      rw [hswap (fun i j => -(rad i j / 2) * x j ^ 2)]
      exact Finset.sum_congr rfl (fun j _ => (Finset.sum_mul _ _ _).symm)
    have hmerge : ∀ i : Fin k,
        ((uK \ {i}).sum (fun j => -(rad i j / 2)) + (uK \ {i}).sum (fun j => -(rad j i / 2)))
          = -((uK \ {i}).sum (fun j => (rad i j + rad j i) / 2)) := by
      intro i
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    calc (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * (x i ^ 2 + x j ^ 2)))
        = (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * x i ^ 2))
          + (uK.sum fun i => (uK \ {i}).sum (fun j => -(rad i j / 2) * x j ^ 2)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_congr rfl (fun j _ => mul_add _ _ _)]
          exact Finset.sum_add_distrib
      _ = (uK.sum fun i => ((uK \ {i}).sum (fun j => -(rad i j / 2))) * x i ^ 2)
          + (uK.sum fun j => ((uK \ {j}).sum (fun i => -(rad i j / 2))) * x j ^ 2) := by
          rw [hA, hB]
      _ = -(uK.sum fun i => ((uK \ {i}).sum fun j => (rad i j + rad j i) / 2) * x i ^ 2) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← add_mul, hmerge i]
          ring
  rw [hO, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- L1 (record 1115 s3c, Gershgorin-free): a positive diagonal plus an entrywise-bounded
perturbation keeps the quadratic form nonnegative whenever every diagonal slack is strictly
positive. Box-robust: it holds for EVERY real perturbation E with `|E i j| <= rad i j`. -/
theorem qform_nonneg_whitenedBox {d : Fin k → ℝ} (rad : Matrix (Fin k) (Fin k) ℝ)
    (hdpos : ∀ i, 0 < d i) (hradpos : ∀ i j, 0 ≤ rad i j)
    (hslack : ∀ i, rad i i + ((uK \ {i}).sum fun j => (rad i j + rad j i) / 2) < d i)
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
      rw [hAjj]
      nlinarith [(abs_le.mp (heb j j)).1, sq_nonneg (x j)]
    · -- i != j : off-diagonal. A ij = E_ij; the AM-GM bound controls the cross term.
      have hAij : A i j = E i j := by dsimp only [A]; simp [h]
      rw [hAij]
      have hxy : -|(E i j) * (x i * x j)| ≤ E i j * x i * x j := by
        rw [mul_assoc]
        exact neg_abs_le _
      have hab : |(E i j) * (x i * x j)| ≤ (rad i j / 2) * (x i ^ 2 + x j ^ 2) := by
        calc
          _ = |E i j| * |x i * x j| := by rw [abs_mul]
          _ ≤ rad i j * |x i * x j| := by
              apply mul_le_mul_of_nonneg_right (heb i j)
              exact abs_nonneg _
          _ ≤ rad i j * ((x i ^ 2 + x j ^ 2) / 2) := by
              have hinner : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
                nlinarith [two_abs_mul_le_sq_add_sq (x i) (x j)]
              exact mul_le_mul_of_nonneg_left hinner (hradpos i j)
          _ = (rad i j / 2) * (x i ^ 2 + x j ^ 2) := by ring
      refine le_trans ?_ hxy
      linarith [hab]
  -- Sum the pointwise lower bound over all pairs.
  have hsum : (uK.sum fun i => uK.sum fun j => (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2))) ≤
      (uK.sum fun i => uK.sum fun j => A i j * x i * x j) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hLB i j
  -- Each collected diagonal coefficient is strictly positive by the slack.
  have hpos : ∀ i, 0 < d i - rad i i - (uK \ {i}).sum fun j => (rad i j + rad j i) / 2 := by
    intro i; linarith [hslack i]
  have hnonneg : 0 ≤ uK.sum fun i => (d i - rad i i - (uK \ {i}).sum fun j => (rad i j + rad j i) / 2) * x i ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hpos i)) (sq_nonneg (x i))
  calc
    0 ≤ uK.sum fun i => (d i - rad i i - (uK \ {i}).sum fun j => (rad i j + rad j i) / 2) * x i ^ 2 := hnonneg
    _ = uK.sum fun i => uK.sum fun j => (if i = j then (d i - rad i i) * x i ^ 2 else -(rad i j / 2) * (x i ^ 2 + x j ^ 2)) := by rw [lbCollect rad x]
    _ ≤ uK.sum fun i => uK.sum fun j => A i j * x i * x j := hsum
    _ = x ⬝ᵥ (A *ᵥ x) := (qformDoubleSum x).symm

end ConnesWeilRH.Source.C1GateLevelTransfer
