/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramScale

/-!
# Record 1127: exact parity reduction of the class Gram owner

The class bump is even and the first eight Legendre factors have their
standard parity.  Opposite-parity products are therefore odd, so their
whole-line Gram integrals vanish exactly.  The committed q28/q38/q48 boxes
contain zero on these entries.  This is a genuine analytic reduction of the
Hbox-G obligation; the same-parity integral enclosures remain open.

RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramParity

open MeasureTheory
open C1ClassWindowObjects
open C1ClassGramOwner
open C1HboxRationalData
open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Finite parity identities -/

/-- The class bump is even. -/
theorem classBump_neg (x : ℝ) : classBump (-x) = classBump x := by
  simp [classBump]

/-- The first eight Legendre factors have the standard parity. -/
theorem legendrePoly_eval_neg_fin8 (i : Fin 8) (x : ℝ) :
    eval (-x) (legendrePoly (i : ℕ)) =
      (-1 : ℝ) ^ (i : ℕ) * eval x (legendrePoly (i : ℕ)) := by
  fin_cases i <;> simp [legendrePoly] <;> ring

/-- The real class-window core has the corresponding parity. -/
theorem classWindowFun_neg (a : ℝ) (i : Fin 8) (x : ℝ) :
    classWindowFun a (i : ℕ) (-x) =
      (-1 : ℝ) ^ (i : ℕ) * classWindowFun a (i : ℕ) x := by
  have hdiv : (-x) / a = -(x / a) := by ring
  change eval ((-x) / a) (legendrePoly (i : ℕ)) * classBump ((-x) / a) =
    (-1 : ℝ) ^ (i : ℕ) *
      (eval (x / a) (legendrePoly (i : ℕ)) * classBump (x / a))
  rw [hdiv, legendrePoly_eval_neg_fin8, classBump_neg]
  ring

/-! ## Odd Gram entries -/

theorem classGramEntry_zero_of_odd_parity
    (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    classGramEntry a ha i j = 0 := by
  let f : ℝ → ℝ := fun x =>
    classWindowFun a (i : ℕ) x * classWindowFun a (j : ℕ) x
  have hpow : (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) = -1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    simp [pow_add]
  have hpoint : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    rw [classWindowFun_neg a i, classWindowFun_neg a j]
    calc
      (-1 : ℝ) ^ (i : ℕ) * classWindowFun a (i : ℕ) x *
          ((-1 : ℝ) ^ (j : ℕ) * classWindowFun a (j : ℕ) x) =
        ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (j : ℕ)) *
          (classWindowFun a (i : ℕ) x * classWindowFun a (j : ℕ) x) := by ring
      _ = (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) *
          (classWindowFun a (i : ℕ) x * classWindowFun a (j : ℕ) x) := by
        rw [← pow_add]
      _ = -(classWindowFun a (i : ℕ) x * classWindowFun a (j : ℕ) x) := by
        simp [hpow]
  have hsym : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x :=
    integral_neg_eq_self f (volume : Measure ℝ)
  have hneg : (∫ x : ℝ, f (-x)) = -∫ x : ℝ, f x := by
    calc
      (∫ x : ℝ, f (-x)) = ∫ x : ℝ, -f x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = -∫ x : ℝ, f x := by rw [integral_neg]
  have hz : (∫ x : ℝ, f x) = 0 := by
    linarith [hsym, hneg]
  simpa [classGramEntry, f] using hz

/-! ## The committed boxes cross zero on the odd entries -/

theorem zero_mem_odd_box_q28 :
    ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo_q28 i j ≤ 0 ∧ 0 ≤ GHi_q28 i j := by
  intro i j hodd
  fin_cases i <;> fin_cases j
  all_goals
    rcases hodd with ⟨k, hk⟩
    have hmod := congrArg (fun n : ℕ => n % 2) hk
    norm_num [Nat.add_mod, Nat.mul_mod] at hmod
    all_goals norm_num [GLo_q28, GHi_q28]

theorem zero_mem_odd_box_q38 :
    ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo_q38 i j ≤ 0 ∧ 0 ≤ GHi_q38 i j := by
  intro i j hodd
  fin_cases i <;> fin_cases j
  all_goals
    rcases hodd with ⟨k, hk⟩
    have hmod := congrArg (fun n : ℕ => n % 2) hk
    norm_num [Nat.add_mod, Nat.mul_mod] at hmod
    all_goals norm_num [GLo_q38, GHi_q38]

theorem zero_mem_odd_box_q48 :
    ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo_q48 i j ≤ 0 ∧ 0 ≤ GHi_q48 i j := by
  intro i j hodd
  fin_cases i <;> fin_cases j
  all_goals
    rcases hodd with ⟨k, hk⟩
    have hmod := congrArg (fun n : ℕ => n % 2) hk
    norm_num [Nat.add_mod, Nat.mul_mod] at hmod
    all_goals norm_num [GLo_q48, GHi_q48]

/-! ## Hbox-facing partial discharge -/

theorem classGram_odd_bounds
    (a : ℝ) (ha : 0 < a) (GLo GHi : Matrix (Fin 8) (Fin 8) ℝ)
    (hboxOdd : ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo i j ≤ 0 ∧ 0 ≤ GHi i j) :
    ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo i j ≤ classGramMatrix a ha i j ∧
        classGramMatrix a ha i j ≤ GHi i j := by
  intro i j hodd
  rw [classGramMatrix_apply, classGramEntry_zero_of_odd_parity a ha i j hodd]
  exact hboxOdd i j hodd

theorem q28_classGram_odd_bounds
    (a : ℝ) (ha : 0 < a) :
    ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo_q28 i j ≤ classGramMatrix a ha i j ∧
        classGramMatrix a ha i j ≤ GHi_q28 i j := by
  intro i j hodd
  rw [classGramMatrix_apply,
    classGramEntry_zero_of_odd_parity a ha i j hodd]
  exact zero_mem_odd_box_q28 i j hodd

end
end C1ClassGramParity
end Source
end ConnesWeilRH
