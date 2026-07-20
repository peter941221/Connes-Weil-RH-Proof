/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCutoffTraceAnomaly
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Finite central-anomaly and boundary-completion guard

This module separates the physical boundary charge from the charge of an
equal-rank completion.  It also records that a finite-dimensional
multiplicative commutator has determinant one.  Consequently, a nonzero
infinite trace anomaly cannot be recovered from finite determinant algebra
without retaining explicit boundary-completion data.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCentralAnomalyGuard

open scoped BigOperators Matrix

open CCM24FiniteSCutoffTraceAnomaly

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Replacing a set of physical boundary modes by padding modes changes the
relative detector trace by exactly `removed charge - padding charge`. -/
theorem boundaryCompletion_response_eq_removed_sub_padding
    (detector : Matrix X X ℂ) (retained removed padding : Finset X)
    (hremoved : Disjoint retained removed)
    (hpadding : Disjoint retained padding) :
    Matrix.trace
        (detector *
          (coordinateProjection (retained ∪ removed) -
            coordinateProjection (retained ∪ padding))) =
      (∑ x ∈ removed, detector x x) - ∑ x ∈ padding, detector x x := by
  rw [mul_sub, Matrix.trace_sub,
    trace_mul_coordinateProjection_eq_sum,
    trace_mul_coordinateProjection_eq_sum,
    Finset.sum_union hremoved, Finset.sum_union hpadding]
  ring

/-- For equal-size removed and padding sets with constant charges on each
piece, the response is the common rank times the charge mismatch. -/
theorem equalCard_boundaryCompletion_response_eq_card_mul_sub
    (detector : Matrix X X ℂ) (retained removed padding : Finset X)
    (physicalValue paddingValue : ℂ)
    (hremovedDisjoint : Disjoint retained removed)
    (hpaddingDisjoint : Disjoint retained padding)
    (hremoved : ∀ x ∈ removed, detector x x = physicalValue)
    (hpadding : ∀ x ∈ padding, detector x x = paddingValue)
    (hcard : removed.card = padding.card) :
    Matrix.trace
        (detector *
          (coordinateProjection (retained ∪ removed) -
            coordinateProjection (retained ∪ padding))) =
      (removed.card : ℂ) * (physicalValue - paddingValue) := by
  rw [boundaryCompletion_response_eq_removed_sub_padding detector retained
    removed padding hremovedDisjoint hpaddingDisjoint]
  have hremovedSum :
      (∑ x ∈ removed, detector x x) =
        (removed.card : ℂ) * physicalValue := by
    calc
      (∑ x ∈ removed, detector x x) =
          ∑ _x ∈ removed, physicalValue := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hremoved x hx
      _ = (removed.card : ℂ) * physicalValue := by simp
  have hpaddingSum :
      (∑ x ∈ padding, detector x x) =
        (padding.card : ℂ) * paddingValue := by
    calc
      (∑ x ∈ padding, detector x x) =
          ∑ _x ∈ padding, paddingValue := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpadding x hx
      _ = (padding.card : ℂ) * paddingValue := by simp
  rw [hremovedSum, hpaddingSum, hcard]
  ring

/-- Two equal-rank completions of the same physical cutoff differ only by
their padding charges.  Strong convergence of the underlying projections does
not appear in, and therefore cannot determine, this finite counterterm. -/
theorem boundaryCompletion_response_sub_eq_paddingDifference
    (detector : Matrix X X ℂ)
    (retained removed padding₁ padding₂ : Finset X)
    (hremoved : Disjoint retained removed)
    (hpadding₁ : Disjoint retained padding₁)
    (hpadding₂ : Disjoint retained padding₂) :
    Matrix.trace
          (detector *
            (coordinateProjection (retained ∪ removed) -
              coordinateProjection (retained ∪ padding₁))) -
        Matrix.trace
          (detector *
            (coordinateProjection (retained ∪ removed) -
              coordinateProjection (retained ∪ padding₂))) =
      (∑ x ∈ padding₂, detector x x) -
        ∑ x ∈ padding₁, detector x x := by
  rw [boundaryCompletion_response_eq_removed_sub_padding detector retained
      removed padding₁ hremoved hpadding₁,
    boundaryCompletion_response_eq_removed_sub_padding detector retained
      removed padding₂ hremoved hpadding₂]
  ring

/-- A finite-dimensional multiplicative commutator has determinant one.
Therefore a nontrivial Toeplitz central anomaly is necessarily an
infinite-boundary effect, not a finite determinant invariant. -/
theorem det_multiplicativeCommutator_eq_one
    (left right leftInverse rightInverse : Matrix X X ℂ)
    (hleft : left * leftInverse = 1)
    (hright : right * rightInverse = 1) :
    Matrix.det (left * right * leftInverse * rightInverse) = 1 := by
  have hleftDet : Matrix.det left * Matrix.det leftInverse = 1 := by
    rw [← Matrix.det_mul, hleft, Matrix.det_one]
  have hrightDet : Matrix.det right * Matrix.det rightInverse = 1 := by
    rw [← Matrix.det_mul, hright, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det left * Matrix.det right * Matrix.det leftInverse *
          Matrix.det rightInverse =
        (Matrix.det left * Matrix.det leftInverse) *
          (Matrix.det right * Matrix.det rightInverse) := by ring
    _ = 1 := by rw [hleftDet, hrightDet, one_mul]

end CCM24FiniteSCentralAnomalyGuard
end CCM25Concrete
end Source
end ConnesWeilRH
