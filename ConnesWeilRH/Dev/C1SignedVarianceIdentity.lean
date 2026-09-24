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

end C1SignedVarianceIdentity
end Source
end ConnesWeilRH
