/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The (gamma) coercivity sandwich for certified spectral data

This leaf is the Lean consumption contract for the (gamma) payload of GATE 1.
The T-side spectral block feeding `cc20TCoercivity_of_spectralBlock` needs
two operator-level spectral facts, `hspectral` (a defect-form lower bound)
and `hR_upper` (a Rayleigh-quotient upper bound on the orthogonal residual).
Both will be produced by a certified row-band enclosure of the concrete
equation-(119) matrix:

* real diagonal centres `center`,
* a symmetric per-entry radius `rad` enclosing the off-diagonal norms,
* the row-dominance bands `center i - sum_j rad i j >= lambda` (lower) or
  `center i + sum_j rad i j <= lambda` (upper).

The two sandwich lemmas here fold that data into whole-space quadratic-form
bounds without ever evaluating the matrix; this is the "floats generate,
Lean verifies the aggregate" pattern of `C1CC20Eq115MassBound` moved from
the L1 side to the spectral side.  The proof is the elementary AM-GM fold
over a symmetric radius - no Hermiticity of `M` is needed, the radius
symmetry carries the whole role - so the aggregate stays a finite `Finset`
computation and no Mathlib spectral calculus is required.

Reference: equation (119) of <https://arxiv.org/html/2006.13771>; companion
records docs/proofs/1046, docs/proofs/1047.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20GammaCoercivity

/-- The Hermitian matrix form of a complex matrix `M` against coefficient
vectors `x`: `sum i j, re (conj (x i) * M i j * x j)`. -/
noncomputable def cc20MatrixForm {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (x : n -> Complex) : Real :=
  ∑ i, ∑ j, (star (x i) * M i j * x j).re

private theorem norm_sq_eq_normSq (z : ℂ) : ‖z‖ ^ 2 = Complex.normSq z := by
  rw [Complex.norm_def, pow_two, Real.mul_self_sqrt (Complex.normSq_nonneg _)]

/-- The diagonal summand of the matrix form of a matrix whose diagonal is
the real scalar `c`. -/
private theorem cc20DiagTerm_re (z : ℂ) (c : Real) :
    (star z * (c : ℂ) * z).re = c * ‖z‖ ^ 2 := by
  have hmul : star z * (c : ℂ) * z = ((c * Complex.normSq z : Real) : ℂ) := by
    rw [mul_comm (star z) ((c : ℂ)), mul_assoc]
    simp only [Complex.star_def]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul]
  rw [hmul, Complex.ofReal_re, ← norm_sq_eq_normSq]

/-- Split the double sum into its diagonal and its off-diagonal rows. -/
private theorem cc20MatrixForm_split {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (x : n -> Complex) :
    cc20MatrixForm M x =
      (∑ i, (star (x i) * M i i * x i).re) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, (star (x i) * M i j * x j).re := by
  unfold cc20MatrixForm
  refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.sum_add_distrib
  rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- The AM-GM fold for one coordinate-square weighting: symmetric radii
fold the double sum of `a i * a j * rad i j` into the row sums. -/
private theorem cc20AmgmFold {n : Type*} [Fintype n]
    (a : n -> Real) (rad : n -> n -> Real)
    (hrnonneg : ∀ i j, 0 ≤ rad i j) (hrsymm : ∀ i j, rad i j = rad j i) :
    ∑ i, ∑ j, a i * a j * rad i j ≤
      ∑ i, a i ^ 2 * ∑ j, rad i j := by
  have hdouble : 2 * ∑ i, ∑ j, a i * a j * rad i j ≤
      ∑ i, ∑ j, (a i ^ 2 + a j ^ 2) * rad i j := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hab : 2 * a i * a j ≤ a i ^ 2 + a j ^ 2 := by
      nlinarith [sq_nonneg (a i - a j)]
    have hmul := mul_le_mul_of_nonneg_right hab (hrnonneg i j)
    nlinarith
  have hsplit : ∑ i, ∑ j, (a i ^ 2 + a j ^ 2) * rad i j =
      (∑ i, a i ^ 2 * ∑ j, rad i j) + (∑ i, a i ^ 2 * ∑ j, rad i j) := by
    rw [show (∑ i, ∑ j, (a i ^ 2 + a j ^ 2) * rad i j) =
        (∑ i, ∑ j, (a i ^ 2 * rad i j + a j ^ 2 * rad i j)) from by
          simp only [add_mul]]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum, Finset.sum_congr rfl fun i _ => hrsymm i j]
  linarith

/-- **Lower sandwich.**  A matrix whose real diagonal centres dominate the
symmetric row radii by `lambda` has its matrix form bounded below by
`lambda` times the coordinate norm square. -/
theorem cc20MatrixForm_ge_of_rowBand
    {n : Type*} [Fintype n]
    (M : Matrix n n ℂ)
    (center : n -> Real) (hc : ∀ i, M i i = (center i : ℂ))
    (rad : n -> n -> Real) (hrdiag : ∀ i, rad i i = 0)
    (hrsymm : ∀ i j, rad i j = rad j i)
    (hrent : ∀ i j, i ≠ j -> ‖M i j‖ ≤ rad i j)
    {lambda : Real} (hband : ∀ i, lambda ≤ center i - ∑ j, rad i j) :
    ∀ x : n -> Complex,
      lambda * ∑ i, ‖x i‖ ^ 2 ≤ cc20MatrixForm M x := by
  intro x
  classical
  have hradnn : ∀ i j, 0 ≤ rad i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hrdiag]
    · exact (norm_nonneg _).trans (hrent i j hij)
  have hdiag : ∑ i, (star (x i) * M i i * x i).re =
      ∑ i, center i * ‖x i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, cc20DiagTerm_re]
  have hterm : ∀ i j, i ≠ j ->
      (star (x i) * M i j * x j).re ≥ -(‖x i‖ * ‖x j‖ * rad i j) := by
    intro i j hij
    have hneg : -(‖star (x i) * M i j * x j‖) ≤
        (star (x i) * M i j * x j).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    have hnorm : ‖star (x i) * M i j * x j‖ = ‖x i‖ * ‖x j‖ * ‖M i j‖ := by
      rw [norm_mul, norm_mul]
      simp only [Complex.star_def, Complex.norm_conj]
      ring
    have hMle : ‖x i‖ * ‖x j‖ * ‖M i j‖ ≤ ‖x i‖ * ‖x j‖ * rad i j :=
      mul_le_mul_of_nonneg_left (hrent i j hij)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc (star (x i) * M i j * x j).re ≥ -(‖star (x i) * M i j * x j‖) := hneg
      _ = -(‖x i‖ * ‖x j‖ * ‖M i j‖) := by rw [hnorm]
      _ ≥ -(‖x i‖ * ‖x j‖ * rad i j) := neg_le_neg hMle
  have hamgm : ∑ i, ∑ j, ‖x i‖ * ‖x j‖ * rad i j ≤
      ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j :=
    cc20AmgmFold (fun i => ‖x i‖) rad hradnn hrsymm
  have hoff : ∑ i, ∑ j ∈ Finset.univ.erase i,
      (star (x i) * M i j * x j).re ≥
      -(∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j) := by
    have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i,
        (star (x i) * M i j * x j).re ≥
        ∑ i, ∑ j ∈ Finset.univ.erase i, -(‖x i‖ * ‖x j‖ * rad i j) :=
      Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j hj =>
          hterm i j (Finset.mem_erase.mp hj).1.symm
    have h2 : ∑ i, ∑ j ∈ Finset.univ.erase i, -(‖x i‖ * ‖x j‖ * rad i j) =
        -(∑ i, ∑ j ∈ Finset.univ.erase i, ‖x i‖ * ‖x j‖ * rad i j) := by
      simp_rw [Finset.sum_neg_distrib]
    have h3 : ∑ i, ∑ j ∈ Finset.univ.erase i, ‖x i‖ * ‖x j‖ * rad i j ≤
        ∑ i, ∑ j, ‖x i‖ * ‖x j‖ * rad i j :=
      Finset.sum_le_sum fun i _ => by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (hradnn i i))
    calc ∑ i, ∑ j ∈ Finset.univ.erase i, (star (x i) * M i j * x j).re
        ≥ ∑ i, ∑ j ∈ Finset.univ.erase i, -(‖x i‖ * ‖x j‖ * rad i j) := h1
      _ = -(∑ i, ∑ j ∈ Finset.univ.erase i, ‖x i‖ * ‖x j‖ * rad i j) := h2
      _ ≥ -(∑ i, ∑ j, ‖x i‖ * ‖x j‖ * rad i j) := neg_le_neg h3
      _ ≥ -(∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j) := neg_le_neg hamgm
  have hbandfold : lambda * ∑ i, ‖x i‖ ^ 2 ≤
      ∑ i, center i * ‖x i‖ ^ 2 - ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j := by
    have hge : ∑ i, lambda * ‖x i‖ ^ 2 ≤
        ∑ i, (center i - ∑ j, rad i j) * ‖x i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hband i) (sq_nonneg _)
    calc lambda * ∑ i, ‖x i‖ ^ 2 = ∑ i, lambda * ‖x i‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, (center i - ∑ j, rad i j) * ‖x i‖ ^ 2 := hge
      _ = ∑ i, (center i * ‖x i‖ ^ 2 - ‖x i‖ ^ 2 * ∑ j, rad i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sub_mul, mul_comm (∑ j, rad i j) (‖x i‖ ^ 2)]
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [cc20MatrixForm_split, hdiag]
  linarith

/-- **Upper sandwich.**  The same data with the upper band gives the
Rayleigh-quotient shape consumed as `hR_upper` after the basis bridge. -/
theorem cc20MatrixForm_le_of_rowBand
    {n : Type*} [Fintype n]
    (M : Matrix n n ℂ)
    (center : n -> Real) (hc : ∀ i, M i i = (center i : ℂ))
    (rad : n -> n -> Real) (hrdiag : ∀ i, rad i i = 0)
    (hrsymm : ∀ i j, rad i j = rad j i)
    (hrent : ∀ i j, i ≠ j -> ‖M i j‖ ≤ rad i j)
    {lambda : Real} (hband : ∀ i, center i + ∑ j, rad i j ≤ lambda) :
    ∀ x : n -> Complex,
      cc20MatrixForm M x ≤ lambda * ∑ i, ‖x i‖ ^ 2 := by
  intro x
  classical
  have hradnn : ∀ i j, 0 ≤ rad i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [hrdiag]
    · exact (norm_nonneg _).trans (hrent i j hij)
  have hdiag : ∑ i, (star (x i) * M i i * x i).re =
      ∑ i, center i * ‖x i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, cc20DiagTerm_re]
  have hterm : ∀ i j, i ≠ j ->
      (star (x i) * M i j * x j).re ≤ ‖x i‖ * ‖x j‖ * rad i j := by
    intro i j hij
    have hpos : (star (x i) * M i j * x j).re ≤
        ‖star (x i) * M i j * x j‖ :=
      (abs_le.mp (Complex.abs_re_le_norm _)).2
    have hnorm : ‖star (x i) * M i j * x j‖ = ‖x i‖ * ‖x j‖ * ‖M i j‖ := by
      rw [norm_mul, norm_mul]
      simp only [Complex.star_def, Complex.norm_conj]
      ring
    have hMle : ‖x i‖ * ‖x j‖ * ‖M i j‖ ≤ ‖x i‖ * ‖x j‖ * rad i j :=
      mul_le_mul_of_nonneg_left (hrent i j hij)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc (star (x i) * M i j * x j).re ≤ ‖star (x i) * M i j * x j‖ := hpos
      _ = ‖x i‖ * ‖x j‖ * ‖M i j‖ := hnorm
      _ ≤ ‖x i‖ * ‖x j‖ * rad i j := hMle
  have hamgm : ∑ i, ∑ j, ‖x i‖ * ‖x j‖ * rad i j ≤
      ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j :=
    cc20AmgmFold (fun i => ‖x i‖) rad hradnn hrsymm
  have hoff : ∑ i, ∑ j ∈ Finset.univ.erase i,
      (star (x i) * M i j * x j).re ≤
      ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j := by
    have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i,
        (star (x i) * M i j * x j).re ≤
        ∑ i, ∑ j ∈ Finset.univ.erase i, ‖x i‖ * ‖x j‖ * rad i j :=
      Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j hj =>
          hterm i j (Finset.mem_erase.mp hj).1.symm
    have h3 : ∑ i, ∑ j ∈ Finset.univ.erase i, ‖x i‖ * ‖x j‖ * rad i j ≤
        ∑ i, ∑ j, ‖x i‖ * ‖x j‖ * rad i j :=
      Finset.sum_le_sum fun i _ => by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        exact le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (hradnn i i))
    calc ∑ i, ∑ j ∈ Finset.univ.erase i, (star (x i) * M i j * x j).re
        ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, ‖x i‖ * ‖x j‖ * rad i j := h1
      _ ≤ ∑ i, ∑ j, ‖x i‖ * ‖x j‖ * rad i j := h3
      _ ≤ ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j := hamgm
  have hbandfold : ∑ i, center i * ‖x i‖ ^ 2 +
      ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j ≤ lambda * ∑ i, ‖x i‖ ^ 2 := by
    have hge : ∑ i, (center i + ∑ j, rad i j) * ‖x i‖ ^ 2 ≤
        ∑ i, lambda * ‖x i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hband i) (sq_nonneg _)
    calc ∑ i, center i * ‖x i‖ ^ 2 + ∑ i, ‖x i‖ ^ 2 * ∑ j, rad i j
        = ∑ i, (center i + ∑ j, rad i j) * ‖x i‖ ^ 2 := by
            refine ((Eq.symm Finset.sum_add_distrib)).trans ?_
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [add_mul, mul_comm (‖x i‖ ^ 2) (∑ j, rad i j)]
      _ ≤ ∑ i, lambda * ‖x i‖ ^ 2 := hge
      _ = lambda * ∑ i, ‖x i‖ ^ 2 := by rw [← Finset.mul_sum]
  rw [cc20MatrixForm_split, hdiag]
  linarith

end C1CC20GammaCoercivity
end Source
end ConnesWeilRH
