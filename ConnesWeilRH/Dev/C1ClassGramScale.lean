/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramOwner

/-!
# Record 1126: exact scale normalization for the class Gram owner

The class-window core has the form `phi_i^a(x) = phi_i^1(x / a)`.  The
whole-line change of variables therefore gives an exact factor `a` in every
Gram entry.  This record exposes that ownership identity and the generic
entrywise-bound transport consumed by the Stage-B `Hbox` chain.

The optional q38/q48 rebase below is only rational comparison of committed
box endpoints.  It does not certify any integral enclosure.  RH is NOT
claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramScale

open MeasureTheory
open C1ClassWindowObjects
open C1ClassGramOwner
open C1HboxRationalData
open Matrix
open scoped BigOperators

noncomputable section

/-- The unit-scale real core is the normalized class-window shape. -/
noncomputable def classGramUnitEntry (i j : Fin 8) : ℝ :=
  classGramEntry 1 (by norm_num) i j

/-- The unit-scale Gram matrix. -/
noncomputable def classGramUnitMatrix : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => classGramUnitEntry i j

@[simp] theorem classGramUnitEntry_apply (i j : Fin 8) :
    classGramUnitMatrix i j = classGramUnitEntry i j :=
  rfl

/-- Scaling the argument restores the unit-scale class-window core. -/
theorem classWindowFun_scale (a : ℝ) (ha : 0 < a) (i : ℕ) (x : ℝ) :
    classWindowFun a i (a * x) = classWindowFun 1 i x := by
  have hax : a * x / a = x := by
    field_simp [ne_of_gt ha]
  simp [classWindowFun, hax]

/-- Every Gram entry scales exactly by the positive class scale. -/
theorem classGramEntry_scale (a : ℝ) (ha : 0 < a) (i j : Fin 8) :
    classGramEntry a ha i j = a * classGramUnitEntry i j := by
  let f : ℝ → ℝ := fun x =>
    classWindowFun 1 (i : ℕ) x * classWindowFun 1 (j : ℕ) x
  have hchange := Measure.integral_comp_div f a
  calc
    classGramEntry a ha i j = ∫ x : ℝ, f (x / a) := by
      unfold classGramEntry
      apply integral_congr_ae
      filter_upwards [] with x
      simp [f, classWindowFun]
    _ = |a| • ∫ y : ℝ, f y := hchange
    _ = a * classGramUnitEntry i j := by
      rw [abs_of_pos ha]
      simp [f, classGramUnitEntry, classGramEntry, smul_eq_mul]

/-- The entire class Gram matrix is a scalar multiple of its unit owner. -/
theorem classGramMatrix_scale (a : ℝ) (ha : 0 < a) :
    classGramMatrix a ha = a • classGramUnitMatrix := by
  ext i j
  change classGramEntry a ha i j = a * classGramUnitEntry i j
  exact classGramEntry_scale a ha i j

/-- Generic transport of a unit-owner entrywise enclosure to scale `a`. -/
theorem classGramBounds_of_unitBounds
    (a : ℝ) (ha : 0 < a)
    (GLo GHi : Matrix (Fin 8) (Fin 8) ℝ)
    (hlo : ∀ i j, GLo i j ≤ a * classGramUnitEntry i j)
    (hhi : ∀ i j, a * classGramUnitEntry i j ≤ GHi i j) :
    ∀ i j, GLo i j ≤ classGramMatrix a ha i j ∧
      classGramMatrix a ha i j ≤ GHi i j := by
  intro i j
  rw [classGramMatrix_scale a ha]
  exact ⟨hlo i j, hhi i j⟩

/-! ## Exact rational rebase checks for the committed G boxes -/

set_option maxHeartbeats 2000000000 in
-- reason: 64 exact rational comparisons for the q38 lower and upper boxes
theorem three_halves_q28_GLo_le_q38_GLo :
    ∀ i j, (3 / 2 : ℝ) * GLo_q28 i j ≤ GLo_q38 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals (simp [GLo_q38, GLo_q28] <;> norm_num)

set_option maxHeartbeats 2000000000 in
-- reason: 64 exact rational comparisons for the q38 lower and upper boxes
theorem q38_GHi_le_three_halves_q28_GHi :
    ∀ i j, GHi_q38 i j ≤ (3 / 2 : ℝ) * GHi_q28 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals (simp [GHi_q38, GHi_q28] <;> norm_num)

set_option maxHeartbeats 2000000000 in
-- reason: 64 exact rational comparisons for the q48 lower and upper boxes
theorem two_q28_GLo_le_q48_GLo :
    ∀ i j, (2 : ℝ) * GLo_q28 i j ≤ GLo_q48 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals (simp [GLo_q48, GLo_q28] <;> norm_num)

set_option maxHeartbeats 2000000000 in
-- reason: 64 exact rational comparisons for the q48 lower and upper boxes
theorem q48_GHi_le_two_q28_GHi :
    ∀ i j, GHi_q48 i j ≤ (2 : ℝ) * GHi_q28 i j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals (simp [GHi_q48, GHi_q28] <;> norm_num)

end
end C1ClassGramScale
end Source
end ConnesWeilRH
