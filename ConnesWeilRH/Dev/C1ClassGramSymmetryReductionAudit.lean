/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramSymmetryReduction

namespace ConnesWeilRH
namespace Source
namespace C1ClassGramSymmetryReduction

open C1ClassGramOwner
open C1ClassGramParity
open C1HboxRationalData
open Matrix

#print axioms classGramMatrix_entry_symm
#print axioms hsymGLo_q28
#print axioms hsymGHi_q28
#print axioms hsymGLo_q38
#print axioms hsymGHi_q38
#print axioms hsymGLo_q48
#print axioms hsymGHi_q48
#print axioms full_classGram_bounds_of_upperTriangle
#print axioms q28_classGram_bounds_of_same_parity_upper

example (a : ℝ) (ha : 0 < a) (i j : Fin 8) :
    classGramMatrix a ha i j = classGramMatrix a ha j i :=
  classGramMatrix_entry_symm a ha i j

example (a : ℝ) (ha : 0 < a)
    (hloUpper : ∀ i j : Fin 8, i ≤ j →
      ¬ Odd ((i : ℕ) + (j : ℕ)) →
      GLo_q28 i j ≤ classGramMatrix a ha i j)
    (hhiUpper : ∀ i j : Fin 8, i ≤ j →
      ¬ Odd ((i : ℕ) + (j : ℕ)) →
      classGramMatrix a ha i j ≤ GHi_q28 i j) :
    ∀ i j : Fin 8,
      GLo_q28 i j ≤ classGramMatrix a ha i j ∧
        classGramMatrix a ha i j ≤ GHi_q28 i j :=
  q28_classGram_bounds_of_same_parity_upper a ha hloUpper hhiUpper

end C1ClassGramSymmetryReduction
end Source
end ConnesWeilRH
