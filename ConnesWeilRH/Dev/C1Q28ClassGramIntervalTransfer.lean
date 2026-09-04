/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramMomentModel

/-!
# Record 1131: q28 class-Gram interval transfer

This leaf turns two explicit base-moment intervals into the entrywise q28
Gram enclosure.  The intervals are inputs only: a separate analytic producer
must prove that the actual `classMoment 0` and `classMoment 2` lie in them.
The q28 box is the scale-2 box, so the model is multiplied by two before it
is compared with `GLo_q28` and `GHi_q28`.

RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Q28ClassGramIntervalTransfer

open C1ClassGramMomentModel
open C1ClassGramMomentReduction
open C1ClassGramOwner
open C1ClassGramScale
open C1HboxRationalData
open Matrix

noncomputable section

/-! ## Explicit conditional base-moment intervals -/

noncomputable def q28Moment0Lo : ℝ :=
  (2397466416982805 / 18014398509481984 : ℝ) - (1 / 10 ^ 15 : ℝ)

noncomputable def q28Moment0Hi : ℝ :=
  (2397466416982805 / 18014398509481984 : ℝ) + (1 / 10 ^ 15 : ℝ)

noncomputable def q28Moment2Lo : ℝ :=
  (8817094793947821 / 576460752303423488 : ℝ) - (1 / 10 ^ 15 : ℝ)

noncomputable def q28Moment2Hi : ℝ :=
  (8817094793947821 / 576460752303423488 : ℝ) + (1 / 10 ^ 15 : ℝ)

/-! ## Model-level interval transfer -/

set_option maxHeartbeats 2000000000 in
-- reason: 64 exact rational two-variable interval comparisons
theorem q28_classGramModel_bounds_of_baseMomentBounds
    (I0 I2 : ℝ)
    (hI0 : q28Moment0Lo ≤ I0 ∧ I0 ≤ q28Moment0Hi)
    (hI2 : q28Moment2Lo ≤ I2 ∧ I2 ≤ q28Moment2Hi) :
    ∀ i j : Fin 8,
      GLo_q28 i j ≤ 2 * classGramMomentModel I0 I2 i j ∧
        2 * classGramMomentModel I0 I2 i j ≤ GHi_q28 i j := by
  rcases hI0 with ⟨hI0lo, hI0hi⟩
  rcases hI2 with ⟨hI2lo, hI2hi⟩
  norm_num [q28Moment0Lo, q28Moment0Hi, q28Moment2Lo, q28Moment2Hi]
    at hI0lo hI0hi hI2lo hI2hi
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [classGramMomentModel, GLo_q28, GHi_q28] ;
      constructor <;> norm_num at * <;> linarith

/-! ## Actual-owner and Hbox-facing adapters -/

theorem q28_classGram_bounds_of_baseMomentBounds
    (hI0 : q28Moment0Lo ≤ classMoment 0 ∧
      classMoment 0 ≤ q28Moment0Hi)
    (hI2 : q28Moment2Lo ≤ classMoment 2 ∧
      classMoment 2 ≤ q28Moment2Hi) :
    ∀ i j : Fin 8,
      GLo_q28 i j ≤ classGramMatrix 2 (by norm_num) i j ∧
        classGramMatrix 2 (by norm_num) i j ≤ GHi_q28 i j := by
  intro i j
  have hmodel := q28_classGramModel_bounds_of_baseMomentBounds
    (classMoment 0) (classMoment 2) hI0 hI2 i j
  have hscale : classGramMatrix 2 (by norm_num) i j =
      2 * classGramMomentModel (classMoment 0) (classMoment 2) i j := by
    calc
      classGramMatrix 2 (by norm_num) i j =
          2 * classGramUnitMatrix i j := by
        rw [classGramMatrix_scale 2 (by norm_num)]
        rfl
      _ = 2 * classGramMomentModel (classMoment 0) (classMoment 2) i j := by
        rw [classGramUnitMatrix_eq_classGramMomentModel]
  rw [hscale]
  exact hmodel

theorem q28_hbox_of_baseMomentBounds
    (M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hI0 : q28Moment0Lo ≤ classMoment 0 ∧
      classMoment 0 ≤ q28Moment0Hi)
    (hI2 : q28Moment2Lo ≤ classMoment 2 ∧
      classMoment 2 ≤ q28Moment2Hi)
    (hM : ∀ i j, MLo_q28 i j ≤ M_true i j ∧
      M_true i j ≤ MHi_q28 i j) :
    Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28
      (classGramMatrix 2 (by norm_num)) M_true := by
  apply hbox_of_classGramBounds 2 (by norm_num)
    GLo_q28 GHi_q28 MLo_q28 MHi_q28 M_true
  · exact q28_classGram_bounds_of_baseMomentBounds hI0 hI2
  · exact hM

end
end C1Q28ClassGramIntervalTransfer
end Source
end ConnesWeilRH
