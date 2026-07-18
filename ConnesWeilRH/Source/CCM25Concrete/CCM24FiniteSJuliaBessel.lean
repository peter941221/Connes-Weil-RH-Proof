/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Julia defect-row Bessel calculus

This module assembles pointwise Julia colligation steps into one defect row.
It proves the exact survivor/defect energy telescope and the weighted Bessel
bound for the Gram-normalized range-sine outputs.  The theorem is generic: it
does not assume or manufacture the still-missing finite-S detector dual row.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJuliaBessel

open scoped BigOperators InnerProductSpace

variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- One pulled-back Julia step on a fixed source carrier.

`pythagorean` is the transfer/defect colligation identity.  The range-sine
field is kept separate: its weighted square is bounded by the same defect
slot, which is the post-Gram prime-square gain from Proof 350. -/
structure JuliaDefectStep (H G : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  transfer : H →L[ℂ] H
  defect : H →L[ℂ] G
  rangeSine : H →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  pythagorean : ∀ x : H,
    ‖transfer x‖ ^ 2 + ‖defect x‖ ^ 2 = ‖x‖ ^ 2
  rangeSine_weighted_le_defect : ∀ x : H,
    weight * ‖rangeSine x‖ ^ 2 ≤ ‖defect x‖ ^ 2

/-- The survivor transfer after all Julia steps, in chronological order. -/
def juliaSurvivor :
    List (JuliaDefectStep H G) → H →L[ℂ] H
  | [] => ContinuousLinearMap.id ℂ H
  | step :: steps => juliaSurvivor steps ∘L step.transfer

/-- Sum of the squared defect outputs along the pulled-back transfer path. -/
def juliaDefectEnergy :
    List (JuliaDefectStep H G) → H → ℝ
  | [], _ => 0
  | step :: steps, x =>
      ‖step.defect x‖ ^ 2 +
        juliaDefectEnergy steps (step.transfer x)

/-- Weighted sum of the squared Gram-normalized range-sine outputs. -/
def juliaRangeEnergy :
    List (JuliaDefectStep H G) → H → ℝ
  | [], _ => 0
  | step :: steps, x =>
      step.weight * ‖step.rangeSine x‖ ^ 2 +
        juliaRangeEnergy steps (step.transfer x)

theorem juliaDefectEnergy_nonneg
    (steps : List (JuliaDefectStep H G)) (x : H) :
    0 ≤ juliaDefectEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaDefectEnergy]
  | cons step steps ih =>
      simp only [juliaDefectEnergy]
      exact add_nonneg (sq_nonneg ‖step.defect x‖)
        (ih (step.transfer x))

theorem juliaRangeEnergy_nonneg
    (steps : List (JuliaDefectStep H G)) (x : H) :
    0 ≤ juliaRangeEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaRangeEnergy]
  | cons step steps ih =>
      simp only [juliaRangeEnergy]
      exact add_nonneg
        (mul_nonneg step.weight_nonneg (sq_nonneg ‖step.rangeSine x‖))
        (ih (step.transfer x))

/-- Exact Pythagorean telescope: every Julia defect slot plus the final
survivor has the source norm square. -/
theorem juliaDefectEnergy_add_survivor_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaDefectEnergy steps x + ‖juliaSurvivor steps x‖ ^ 2 = ‖x‖ ^ 2 := by
  induction steps generalizing x with
  | nil => simp [juliaDefectEnergy, juliaSurvivor]
  | cons step steps ih =>
      simp only [juliaDefectEnergy, juliaSurvivor,
        ContinuousLinearMap.comp_apply]
      calc
        ‖step.defect x‖ ^ 2 + juliaDefectEnergy steps (step.transfer x) +
            ‖juliaSurvivor steps (step.transfer x)‖ ^ 2 =
          ‖step.defect x‖ ^ 2 +
            (juliaDefectEnergy steps (step.transfer x) +
              ‖juliaSurvivor steps (step.transfer x)‖ ^ 2) := by
                rw [add_assoc]
        _ = ‖step.defect x‖ ^ 2 + ‖step.transfer x‖ ^ 2 := by
              rw [ih (step.transfer x)]
        _ = ‖x‖ ^ 2 := by
              simpa only [add_comm] using step.pythagorean x

theorem juliaDefectEnergy_le_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaDefectEnergy steps x ≤ ‖x‖ ^ 2 := by
  rw [← juliaDefectEnergy_add_survivor_normSq steps x]
  exact le_add_of_nonneg_right (sq_nonneg ‖juliaSurvivor steps x‖)

/-- The weighted range-sine row is dominated stepwise by the exact Julia
defect row before any summation or absolute value. -/
theorem juliaRangeEnergy_le_defectEnergy
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaRangeEnergy steps x ≤ juliaDefectEnergy steps x := by
  induction steps generalizing x with
  | nil => simp [juliaRangeEnergy, juliaDefectEnergy]
  | cons step steps ih =>
      simp only [juliaRangeEnergy, juliaDefectEnergy]
      exact add_le_add (step.rangeSine_weighted_le_defect x)
        (ih (step.transfer x))

/-- Constant-one weighted Bessel bound for the complete pulled-back range
row. -/
theorem juliaRangeEnergy_le_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaRangeEnergy steps x ≤ ‖x‖ ^ 2 :=
  (juliaRangeEnergy_le_defectEnergy steps x).trans
    (juliaDefectEnergy_le_normSq steps x)

/-- The Bessel estimate amplifies over any summable family of source vectors.
This is the basis-level form used for Hilbert--Schmidt inputs. -/
theorem summable_juliaRangeEnergy
    {ι : Type*} (steps : List (JuliaDefectStep H G)) (vectors : ι → H)
    (hvectors : Summable fun i => ‖vectors i‖ ^ 2) :
    Summable fun i => juliaRangeEnergy steps (vectors i) := by
  exact Summable.of_nonneg_of_le
    (fun i => juliaRangeEnergy_nonneg steps (vectors i))
    (fun i => juliaRangeEnergy_le_normSq steps (vectors i))
    hvectors

/-- The total weighted range energy is no larger than the source square sum. -/
theorem tsum_juliaRangeEnergy_le
    {ι : Type*} (steps : List (JuliaDefectStep H G)) (vectors : ι → H)
    (hvectors : Summable fun i => ‖vectors i‖ ^ 2) :
    ∑' i, juliaRangeEnergy steps (vectors i) ≤
      ∑' i, ‖vectors i‖ ^ 2 := by
  exact (summable_juliaRangeEnergy steps vectors hvectors).tsum_le_tsum
    (fun i => juliaRangeEnergy_le_normSq steps (vectors i))
    hvectors

/-- Named-basis Hilbert--Schmidt amplification of the Julia Bessel row. -/
theorem summable_juliaRangeEnergy_comp
    {ι K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (basis : HilbertBasis ι ℂ K)
    (steps : List (JuliaDefectStep H G)) (operator : K →L[ℂ] H)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2) :
    Summable fun i => juliaRangeEnergy steps (operator (basis i)) :=
  summable_juliaRangeEnergy steps (fun i => operator (basis i)) hoperator

/-! The final finite direct-sum consumer is kept separate from the still-open
detector producer.  A route owner may instantiate `left` with the weighted
Julia range row and `right` with completed detector innovations only after the
same-object endpoint identity has been proved. -/

theorem finite_dual_pairing_norm_le
    {ι : Type*} [Fintype ι]
    (left right : ι → H) :
    ‖∑ i, ⟪left i, right i⟫_ℂ‖ ≤
      Real.sqrt (∑ i, ‖left i‖ ^ 2) *
        Real.sqrt (∑ i, ‖right i‖ ^ 2) := by
  calc
    ‖∑ i, ⟪left i, right i⟫_ℂ‖ ≤
        ∑ i, ‖⟪left i, right i⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖left i‖ * ‖right i‖ := by
      exact Finset.sum_le_sum (fun i _ => norm_inner_le_norm _ _)
    _ ≤ Real.sqrt (∑ i, ‖left i‖ ^ 2) *
          Real.sqrt (∑ i, ‖right i‖ ^ 2) := by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt (s := Finset.univ)
          (f := fun i => ‖left i‖) (g := fun i => ‖right i‖))

end CCM24FiniteSJuliaBessel
end CCM25Concrete
end Source
end ConnesWeilRH
