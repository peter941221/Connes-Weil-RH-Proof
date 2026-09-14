/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3WeightedFiniteStage
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# R3 strong endpoint convergence through an HS detector root

This leaf proves the analytic transfer principle needed by the weighted
two-projection route.  Strong convergence on each detector-root column,
uniform contraction bounds, and one Hilbert--Schmidt square-sum imply
convergence of the weighted square energy.  No operator-norm convergence or
Friedrichs-angle gap is assumed.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open scoped Topology

theorem tendsto_hilbertSchmidt_energy_of_strong_convergence
    {α ι H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H)
    (factor : H →L[ℂ] G)
    (operators : α → G →L[ℂ] G)
    (limit : G →L[ℂ] G)
    (𝓕 : Filter α)
    (hfactor : Summable fun i => ‖factor (basis i)‖ ^ 2)
    (hpoint : ∀ i,
      Tendsto
        (fun a => (operators a - limit) (factor (basis i)))
        𝓕 (𝓝 0))
    (hoperators : ∀ᶠ a in 𝓕, ‖operators a‖ ≤ 1)
    (hlimit : ‖limit‖ ≤ 1) :
    Tendsto
      (fun a => ∑' i,
        ‖(operators a - limit) (factor (basis i))‖ ^ 2)
      𝓕 (𝓝 0) := by
  have hbound : ∀ᶠ a in 𝓕, ∀ i,
      ‖(operators a - limit) (factor (basis i))‖ ^ 2 ≤
        4 * ‖factor (basis i)‖ ^ 2 := by
    filter_upwards [hoperators] with a ha
    intro i
    have hlinear :
        ‖(operators a - limit) (factor (basis i))‖ ≤
          2 * ‖factor (basis i)‖ := by
      calc
        ‖(operators a - limit) (factor (basis i))‖ ≤
            ‖operators a - limit‖ * ‖factor (basis i)‖ :=
          (operators a - limit).le_opNorm _
        _ ≤ (‖operators a‖ + ‖limit‖) *
            ‖factor (basis i)‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ (1 + 1) * ‖factor (basis i)‖ := by
          gcongr
        _ = 2 * ‖factor (basis i)‖ := by ring
    nlinarith [norm_nonneg ((operators a - limit) (factor (basis i))),
      norm_nonneg (factor (basis i))]
  have hbound' : ∀ᶠ a in 𝓕, ∀ i,
      ‖‖(operators a - limit) (factor (basis i))‖ ^ 2‖ ≤
        4 * ‖factor (basis i)‖ ^ 2 := by
    filter_upwards [hbound] with a ha
    intro i
    have hnonneg :
        0 ≤ ‖(operators a - limit) (factor (basis i))‖ ^ 2 :=
      sq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using ha i
  have hsum :
      Tendsto
        (fun a => ∑' i,
          ‖(operators a - limit) (factor (basis i))‖ ^ 2)
        𝓕 (𝓝 (∑' _ : ι, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (hfactor.mul_left (4 : ℝ)) ?_ hbound'
    intro i
    convert (hpoint i).norm.pow 2 using 1 <;> norm_num
  simpa only [tsum_zero] using hsum

end Dev
end ConnesWeilRH
