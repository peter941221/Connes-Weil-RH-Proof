/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramParity

/-!
# Record 1128: symmetric reduction of the class Gram certificate

The real class Gram matrix and the committed G endpoint matrices are
symmetric.  Combined with record 1127's exact odd-entry zero, this reduces a
future full entrywise Hbox-G certificate to the upper-triangle same-parity
entries.  No integral enclosure is asserted here.

RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramSymmetryReduction

open C1ClassGramOwner
open C1ClassGramParity
open C1HboxRationalData
open Matrix

noncomputable section

/-- Entrywise form of the symmetry of the real class Gram matrix. -/
theorem classGramMatrix_entry_symm (a : ℝ) (ha : 0 < a)
    (i j : Fin 8) :
    classGramMatrix a ha i j = classGramMatrix a ha j i := by
  have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M i j)
    (classGramMatrix_transpose a ha)
  simpa using h

/-! ## Exact symmetry of the committed endpoint matrices -/

theorem hsymGLo_q28 : ∀ i j : Fin 8, GLo_q28 i j = GLo_q28 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GLo_q28]

theorem hsymGHi_q28 : ∀ i j : Fin 8, GHi_q28 i j = GHi_q28 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GHi_q28]

theorem hsymGLo_q38 : ∀ i j : Fin 8, GLo_q38 i j = GLo_q38 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GLo_q38]

theorem hsymGHi_q38 : ∀ i j : Fin 8, GHi_q38 i j = GHi_q38 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GHi_q38]

theorem hsymGLo_q48 : ∀ i j : Fin 8, GLo_q48 i j = GLo_q48 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GLo_q48]

theorem hsymGHi_q48 : ∀ i j : Fin 8, GHi_q48 i j = GHi_q48 j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [GHi_q48]

/-! ## Upper-triangle-to-full transport -/

theorem full_classGram_bounds_of_upperTriangle
    (a : ℝ) (ha : 0 < a)
    (GLo GHi : Matrix (Fin 8) (Fin 8) ℝ)
    (hgram : ∀ i j : Fin 8,
      classGramMatrix a ha i j = classGramMatrix a ha j i)
    (hloSym : ∀ i j : Fin 8, GLo i j = GLo j i)
    (hhiSym : ∀ i j : Fin 8, GHi i j = GHi j i)
    (hzero : ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      classGramMatrix a ha i j = 0)
    (hzeroBox : ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      GLo i j ≤ 0 ∧ 0 ≤ GHi i j)
    (hloUpper : ∀ i j : Fin 8, i ≤ j →
      ¬ Odd ((i : ℕ) + (j : ℕ)) →
      GLo i j ≤ classGramMatrix a ha i j)
    (hhiUpper : ∀ i j : Fin 8, i ≤ j →
      ¬ Odd ((i : ℕ) + (j : ℕ)) →
      classGramMatrix a ha i j ≤ GHi i j) :
    ∀ i j : Fin 8,
      GLo i j ≤ classGramMatrix a ha i j ∧
        classGramMatrix a ha i j ≤ GHi i j := by
  intro i j
  by_cases hodd : Odd ((i : ℕ) + (j : ℕ))
  · rw [hzero i j hodd]
    exact hzeroBox i j hodd
  · by_cases hij : i ≤ j
    · exact ⟨hloUpper i j hij hodd, hhiUpper i j hij hodd⟩
    · have hji : j ≤ i := le_of_not_ge hij
      have hodd' : ¬ Odd ((j : ℕ) + (i : ℕ)) := by
        intro h
        apply hodd
        simpa [Nat.add_comm] using h
      constructor
      · rw [hloSym i j, hgram i j]
        exact hloUpper j i hji hodd'
      · rw [hgram i j, hhiSym i j]
        exact hhiUpper j i hji hodd'

/-! ## q28 Hbox-facing reduction -/

theorem q28_classGram_bounds_of_same_parity_upper
    (a : ℝ) (ha : 0 < a)
    (hloUpper : ∀ i j : Fin 8, i ≤ j →
      ¬ Odd ((i : ℕ) + (j : ℕ)) →
      GLo_q28 i j ≤ classGramMatrix a ha i j)
    (hhiUpper : ∀ i j : Fin 8, i ≤ j →
      ¬ Odd ((i : ℕ) + (j : ℕ)) →
      classGramMatrix a ha i j ≤ GHi_q28 i j) :
    ∀ i j : Fin 8,
      GLo_q28 i j ≤ classGramMatrix a ha i j ∧
        classGramMatrix a ha i j ≤ GHi_q28 i j := by
  have hzero : ∀ i j : Fin 8, Odd ((i : ℕ) + (j : ℕ)) →
      classGramMatrix a ha i j = 0 := by
    intro i j hodd
    rw [classGramMatrix_apply,
      classGramEntry_zero_of_odd_parity a ha i j hodd]
  exact full_classGram_bounds_of_upperTriangle a ha GLo_q28 GHi_q28
    (classGramMatrix_entry_symm a ha) hsymGLo_q28 hsymGHi_q28 hzero
    zero_mem_odd_box_q28 hloUpper hhiUpper

end
end C1ClassGramSymmetryReduction
end Source
end ConnesWeilRH
