/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaBessel

/-!
# Weighted detector-row consumer

This module formalizes the abstract arithmetic consumer in Proof 359.  A
nonnegative finite row with one common pointwise energy bound is controlled by
that bound times the total reciprocal weight.  It deliberately does not
construct the source-specific complete detector factors required by Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSHarmonicDetectorRow

open scoped BigOperators

/-- Weighted finite energy of a detector row. -/
def weightedDetectorEnergy
    {ι : Type*} [Fintype ι]
    (weight energy : ι → ℝ) : ℝ :=
  ∑ i, weight i * energy i

/-- A pointwise common energy bound factors out of a nonnegative weighted
finite row. -/
theorem weightedDetectorEnergy_le_weightSum_mul
    {ι : Type*} [Fintype ι]
    (weight energy : ι → ℝ) (commonBound : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (henergy : ∀ i, energy i ≤ commonBound) :
    weightedDetectorEnergy weight energy ≤
      (∑ i, weight i) * commonBound := by
  unfold weightedDetectorEnergy
  calc
    (∑ i, weight i * energy i) ≤
        ∑ i, weight i * commonBound := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (henergy i) (hweight i)
    _ = (∑ i, weight i) * commonBound := by
      rw [Finset.sum_mul]

/-- Combining a total-weight bound with the common pointwise row bound. -/
theorem weightedDetectorEnergy_le
    {ι : Type*} [Fintype ι]
    (weight energy : ι → ℝ) (commonBound totalWeight : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (henergy : ∀ i, energy i ≤ commonBound)
    (hcommon : 0 ≤ commonBound)
    (hweightSum : (∑ i, weight i) ≤ totalWeight) :
    weightedDetectorEnergy weight energy ≤
      totalWeight * commonBound := by
  exact (weightedDetectorEnergy_le_weightSum_mul
    weight energy commonBound hweight henergy).trans
      (mul_le_mul_of_nonneg_right hweightSum hcommon)

end CCM24FiniteSHarmonicDetectorRow
end CCM25Concrete
end Source
end ConnesWeilRH
