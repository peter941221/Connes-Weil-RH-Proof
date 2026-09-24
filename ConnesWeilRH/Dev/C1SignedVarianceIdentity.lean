/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1FourPointSpanGateCertificate

namespace ConnesWeilRH
namespace Source
namespace C1SignedVarianceIdentity

open scoped BigOperators

theorem finite_signed_variance_identity
    {α : Type*} (s : Finset α) (c p : α → ℝ) :
    (∑ i ∈ s, c i * p i ^ 2) * (∑ i ∈ s, c i) -
        (∑ i ∈ s, c i * p i) ^ 2 =
      (1 / 2 : ℝ) *
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * (p i - p j) ^ 2 := by
  classical
  rw [pow_two]
  simp only [Finset.sum_mul_sum]
  simp_rw [sub_sq]
  have hswap :
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * p j ^ 2) =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * p i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  have hExpand :
      (∑ i ∈ s, ∑ j ∈ s,
        (-(c i * c j * p i * p j) +
          c i * c j * p i ^ 2 * (1 / 2) +
          c i * c j * p j ^ 2 * (1 / 2))) =
        (∑ i ∈ s, ∑ j ∈ s, -(c i * c j * p i * p j)) +
          (∑ i ∈ s, ∑ j ∈ s, c i * c j * p i ^ 2 * (1 / 2)) +
          (∑ i ∈ s, ∑ j ∈ s, c i * c j * p j ^ 2 * (1 / 2)) := by
    calc
      _ = ∑ i ∈ s,
          ((∑ j ∈ s, -(c i * c j * p i * p j)) +
            (∑ j ∈ s, c i * c j * p i ^ 2 * (1 / 2)) +
            (∑ j ∈ s, c i * c j * p j ^ 2 * (1 / 2))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hPoly :
      (∑ i ∈ s, ∑ j ∈ s,
        (1 / 2 : ℝ) * (c i * c j * (p i ^ 2 - 2 * p i * p j + p j ^ 2))) =
        ∑ i ∈ s, ∑ j ∈ s,
          (-(c i * c j * p i * p j) +
            c i * c j * p i ^ 2 * (1 / 2) +
            c i * c j * p j ^ 2 * (1 / 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hscaled :
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * p j ^ 2 * (1 / 2)) =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * p i ^ 2 * (1 / 2) := by
    simpa only [Finset.sum_mul] using
      congrArg (fun z : ℝ => z * (1 / 2)) hswap
  rw [hPoly, hExpand]
  rw [hscaled]
  have hdouble :
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * p i ^ 2 * (1 / 2)) * 2 =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * p i ^ 2 := by
    calc
      _ = (∑ i ∈ s, (∑ j ∈ s, c i * c j * p i ^ 2) * (1 / 2)) * 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ = ∑ i ∈ s, ((∑ j ∈ s, c i * c j * p i ^ 2) * (1 / 2)) * 2 := by
        rw [Finset.sum_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hAorder :
      (∑ i ∈ s, ∑ j ∈ s, c i * p i ^ 2 * c j) =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * p i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcross :
      (∑ i ∈ s, ∑ j ∈ s, c i * p i * (c j * p j)) =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * p i * p j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hneg :
      (∑ i ∈ s, ∑ j ∈ s, -(c i * c j * p i * p j)) =
        -(∑ i ∈ s, ∑ j ∈ s, c i * c j * p i * p j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_neg_distrib]
  rw [hAorder, hcross, hneg]
  linarith [hdouble]

theorem two_atom_signed_variance_identity
    (c₀ c₁ p₀ p₁ : ℝ) :
    (c₀ * p₀ ^ 2 + c₁ * p₁ ^ 2) * (c₀ + c₁) -
        (c₀ * p₀ + c₁ * p₁) ^ 2 =
      c₀ * c₁ * (p₀ - p₁) ^ 2 := by
  ring

theorem two_atom_signed_variance_neg
    {c₀ c₁ p₀ p₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 0) (hp : p₀ ≠ p₁) :
    (c₀ * p₀ ^ 2 + c₁ * p₁ ^ 2) * (c₀ + c₁) -
        (c₀ * p₀ + c₁ * p₁) ^ 2 < 0 := by
  rw [two_atom_signed_variance_identity]
  have hdiff : 0 < (p₀ - p₁) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hp)
  have hcprod : c₀ * c₁ < 0 := mul_neg_of_pos_of_neg hc₀ hc₁
  simpa [mul_assoc] using mul_neg_of_neg_of_pos hcprod hdiff

theorem bipartite_double_sum_split
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (hdisj : Disjoint s₁ s₂)
    (F : α → α → ℝ) (hsymm : ∀ i ∈ s₁, ∀ j ∈ s₂, F j i = F i j) :
    ∑ i ∈ s₁ ∪ s₂, ∑ j ∈ s₁ ∪ s₂, F i j =
      (∑ i ∈ s₁, ∑ j ∈ s₁, F i j) +
      (∑ i ∈ s₂, ∑ j ∈ s₂, F i j) +
      2 * ∑ i ∈ s₁, ∑ j ∈ s₂, F i j := by
  have hinner : ∀ i, (∑ j ∈ s₁ ∪ s₂, F i j) = (∑ j ∈ s₁, F i j) + ∑ j ∈ s₂, F i j :=
    fun i => Finset.sum_union hdisj
  simp_rw [hinner]
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ i ∈ s₂, ∑ j ∈ s₁, F i j) = ∑ i ∈ s₁, ∑ j ∈ s₂, F i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun i hi => hsymm j hj i hi))
  linarith [hcross]

/-- The exact bipartite signed variance identity: for any disjoint partition `s₁ ∪ s₂`,
the variance determinant decomposes into internal positive variances on `s₁` and `s₂`
minus the positive-negative cross gap energy. -/
theorem finite_signed_variance_bipartite_identity
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (hdisj : Disjoint s₁ s₂) (c p : α → ℝ) :
    (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) * (∑ i ∈ s₁ ∪ s₂, c i) -
        (∑ i ∈ s₁ ∪ s₂, c i * p i) ^ 2 =
      (1 / 2 : ℝ) * (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) +
      (1 / 2 : ℝ) * (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) -
      ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2 := by
  have hsymm : ∀ i ∈ s₁, ∀ j ∈ s₂,
      c j * c i * (p j - p i) ^ 2 = c i * c j * (p i - p j) ^ 2 := by
    intro i _ j _
    ring
  have hsplit := bipartite_double_sum_split s₁ s₂ hdisj
    (fun i j => c i * c j * (p i - p j) ^ 2) hsymm
  have hvar := finite_signed_variance_identity (s₁ ∪ s₂) c p
  rw [hvar, hsplit]
  have hcross : (∑ i ∈ s₁, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) =
      -∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  linarith [hcross]

/-- Strict bipartite variance-gap negativity criterion: whenever the cross gap energy
strictly dominates the internal positive variances, the variance determinant is
strictly negative. -/
theorem finite_signed_variance_bipartite_neg
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (hdisj : Disjoint s₁ s₂) (c p : α → ℝ)
    (hgap :
      (1 / 2 : ℝ) * (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) +
      (1 / 2 : ℝ) * (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) <
      ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2) :
    (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) * (∑ i ∈ s₁ ∪ s₂, c i) -
        (∑ i ∈ s₁ ∪ s₂, c i * p i) ^ 2 < 0 := by
  rw [finite_signed_variance_bipartite_identity s₁ s₂ hdisj c p]
  linarith

open C1FourPointSpanGateCertificate

/-- Master variance-gap gate certificate: a positive total weight, a positive cross sum,
and the bipartite variance-gap domination condition produce a strictly positive span coefficient
with a strictly negative span gate quadratic. -/
theorem exists_pos_lambda_quadratic_neg_of_bipartite_variance_gap
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (hdisj : Disjoint s₁ s₂) (c p : α → ℝ)
    (hC : 0 < ∑ i ∈ s₁ ∪ s₂, c i)
    (hB : 0 < 2 * ∑ i ∈ s₁ ∪ s₂, c i * p i)
    (hgap :
      (1 / 2 : ℝ) * (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) +
      (1 / 2 : ℝ) * (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) <
      ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2) :
    ∃ lam : ℝ, 0 < lam ∧
      (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) - lam * (2 * ∑ i ∈ s₁ ∪ s₂, c i * p i) +
        lam ^ 2 * (∑ i ∈ s₁ ∪ s₂, c i) < 0 := by
  have hdet :
      (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) * (∑ i ∈ s₁ ∪ s₂, c i) -
        ((2 * ∑ i ∈ s₁ ∪ s₂, c i * p i) / 2) ^ 2 < 0 := by
    have hhalf : (2 * ∑ i ∈ s₁ ∪ s₂, c i * p i) / 2 = ∑ i ∈ s₁ ∪ s₂, c i * p i := by ring
    rw [hhalf]
    exact finite_signed_variance_bipartite_neg s₁ s₂ hdisj c p hgap
  exact exists_pos_lambda_quadratic_neg_of_det_neg hC hB hdet

/-- Macro-atom variance bound: whenever internal oscillations on `s₁` and `s₂` are bounded
by `M₁` and `M₂`, while pairwise differences across `s₁ × s₂` are bounded below by `G`,
the aggregate oscillation condition implies strict negativity of the variance determinant. -/
theorem finite_signed_variance_bipartite_bound_neg
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (hdisj : Disjoint s₁ s₂)
    (c p : α → ℝ)
    (hc₁ : ∀ i ∈ s₁, 0 ≤ c i)
    (hc₂ : ∀ j ∈ s₂, c j ≤ 0)
    (M₁ M₂ G : ℝ)
    (hM₁ : ∀ i ∈ s₁, ∀ i' ∈ s₁, (p i - p i') ^ 2 ≤ M₁)
    (hM₂ : ∀ j ∈ s₂, ∀ j' ∈ s₂, (p j - p j') ^ 2 ≤ M₂)
    (hG : ∀ i ∈ s₁, ∀ j ∈ s₂, G ≤ (p i - p j) ^ 2)
    (hdom :
      (1 / 2 : ℝ) * M₁ * (∑ i ∈ s₁, c i) ^ 2 +
      (1 / 2 : ℝ) * M₂ * (∑ j ∈ s₂, -c j) ^ 2 <
      G * (∑ i ∈ s₁, c i) * (∑ j ∈ s₂, -c j)) :
    (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) * (∑ i ∈ s₁ ∪ s₂, c i) -
        (∑ i ∈ s₁ ∪ s₂, c i * p i) ^ 2 < 0 := by
  have hterm1 : ∀ i ∈ s₁, ∀ j ∈ s₁, c i * c j * (p i - p j) ^ 2 ≤ c i * c j * M₁ := by
    intro i hi j hj
    have hpos : 0 ≤ c i * c j := mul_nonneg (hc₁ i hi) (hc₁ j hj)
    exact mul_le_mul_of_nonneg_left (hM₁ i hi j hj) hpos
  have hsum1 : (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) ≤
      M₁ * (∑ i ∈ s₁, c i) ^ 2 := by
    calc
      (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) ≤
          ∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * M₁ :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm1 i hi j hj
      _ = (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j) * M₁ := by
        simp_rw [← Finset.sum_mul]
      _ = M₁ * (∑ i ∈ s₁, c i) ^ 2 := by
        rw [← Finset.sum_mul_sum, pow_two]
        ring
  have hterm2 : ∀ i ∈ s₂, ∀ j ∈ s₂, c i * c j * (p i - p j) ^ 2 ≤ (-c i) * (-c j) * M₂ := by
    intro i hi j hj
    have hpos : 0 ≤ (-c i) * (-c j) :=
      mul_nonneg (neg_nonneg.mpr (hc₂ i hi)) (neg_nonneg.mpr (hc₂ j hj))
    have heq : c i * c j = (-c i) * (-c j) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hM₂ i hi j hj) hpos
  have hsum2 : (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) ≤
      M₂ * (∑ j ∈ s₂, -c j) ^ 2 := by
    calc
      (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) ≤
          ∑ i ∈ s₂, ∑ j ∈ s₂, (-c i) * (-c j) * M₂ :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = (∑ i ∈ s₂, ∑ j ∈ s₂, (-c i) * (-c j)) * M₂ := by
        simp_rw [← Finset.sum_mul]
      _ = M₂ * (∑ j ∈ s₂, -c j) ^ 2 := by
        rw [← Finset.sum_mul_sum, pow_two]
        ring
  have hterm3 : ∀ i ∈ s₁, ∀ j ∈ s₂, c i * (-c j) * G ≤ c i * (-c j) * (p i - p j) ^ 2 := by
    intro i hi j hj
    have hpos : 0 ≤ c i * (-c j) :=
      mul_nonneg (hc₁ i hi) (neg_nonneg.mpr (hc₂ j hj))
    exact mul_le_mul_of_nonneg_left (hG i hi j hj) hpos
  have hsum3 : G * (∑ i ∈ s₁, c i) * (∑ j ∈ s₂, -c j) ≤
      ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2 := by
    calc
      G * (∑ i ∈ s₁, c i) * (∑ j ∈ s₂, -c j) =
          (∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j)) * G := by
        rw [← Finset.sum_mul_sum]
        ring
      _ = ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * G := by
        simp_rw [← Finset.sum_mul]
      _ ≤ ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm3 i hi j hj
  have hgap :
      (1 / 2 : ℝ) * (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) +
      (1 / 2 : ℝ) * (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) <
      ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2 := by
    calc
      (1 / 2 : ℝ) * (∑ i ∈ s₁, ∑ j ∈ s₁, c i * c j * (p i - p j) ^ 2) +
      (1 / 2 : ℝ) * (∑ i ∈ s₂, ∑ j ∈ s₂, c i * c j * (p i - p j) ^ 2) ≤
          (1 / 2 : ℝ) * (M₁ * (∑ i ∈ s₁, c i) ^ 2) +
          (1 / 2 : ℝ) * (M₂ * (∑ j ∈ s₂, -c j) ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hsum1 (by norm_num))
          (mul_le_mul_of_nonneg_left hsum2 (by norm_num))
      _ = (1 / 2 : ℝ) * M₁ * (∑ i ∈ s₁, c i) ^ 2 +
          (1 / 2 : ℝ) * M₂ * (∑ j ∈ s₂, -c j) ^ 2 := by ring
      _ < G * (∑ i ∈ s₁, c i) * (∑ j ∈ s₂, -c j) := hdom
      _ ≤ ∑ i ∈ s₁, ∑ j ∈ s₂, c i * (-c j) * (p i - p j) ^ 2 := hsum3
  exact finite_signed_variance_bipartite_neg s₁ s₂ hdisj c p hgap

/-- Master macro-atom gate certificate: bounds on positive/negative internal oscillations
and cross separation yield a strictly positive coefficient with strictly negative span gate. -/
theorem exists_pos_lambda_quadratic_neg_of_macro_atom_bounds
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (hdisj : Disjoint s₁ s₂)
    (c p : α → ℝ)
    (hc₁ : ∀ i ∈ s₁, 0 ≤ c i)
    (hc₂ : ∀ j ∈ s₂, c j ≤ 0)
    (M₁ M₂ G : ℝ)
    (hM₁ : ∀ i ∈ s₁, ∀ i' ∈ s₁, (p i - p i') ^ 2 ≤ M₁)
    (hM₂ : ∀ j ∈ s₂, ∀ j' ∈ s₂, (p j - p j') ^ 2 ≤ M₂)
    (hG : ∀ i ∈ s₁, ∀ j ∈ s₂, G ≤ (p i - p j) ^ 2)
    (hC : 0 < ∑ i ∈ s₁ ∪ s₂, c i)
    (hB : 0 < 2 * ∑ i ∈ s₁ ∪ s₂, c i * p i)
    (hdom :
      (1 / 2 : ℝ) * M₁ * (∑ i ∈ s₁, c i) ^ 2 +
      (1 / 2 : ℝ) * M₂ * (∑ j ∈ s₂, -c j) ^ 2 <
      G * (∑ i ∈ s₁, c i) * (∑ j ∈ s₂, -c j)) :
    ∃ lam : ℝ, 0 < lam ∧
      (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) - lam * (2 * ∑ i ∈ s₁ ∪ s₂, c i * p i) +
        lam ^ 2 * (∑ i ∈ s₁ ∪ s₂, c i) < 0 := by
  have hdet :
      (∑ i ∈ s₁ ∪ s₂, c i * p i ^ 2) * (∑ i ∈ s₁ ∪ s₂, c i) -
        ((2 * ∑ i ∈ s₁ ∪ s₂, c i * p i) / 2) ^ 2 < 0 := by
    have hhalf : (2 * ∑ i ∈ s₁ ∪ s₂, c i * p i) / 2 = ∑ i ∈ s₁ ∪ s₂, c i * p i := by ring
    rw [hhalf]
    exact finite_signed_variance_bipartite_bound_neg s₁ s₂ hdisj c p hc₁ hc₂ M₁ M₂ G hM₁ hM₂ hG hdom
  exact exists_pos_lambda_quadratic_neg_of_det_neg hC hB hdet

end C1SignedVarianceIdentity
end Source
end ConnesWeilRH
