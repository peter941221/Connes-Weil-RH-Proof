/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassGramOwner

/-!
# Record 1125 audit: class Gram owner

Focused axiom audit and consumer-shape examples for the same-owner Gram
interface.  The entrywise numerical Hbox-G inequalities remain hypotheses.
RH is NOT claimed.
-/

open ConnesWeilRH Source C1ClassGramOwner
open C1HboxRationalData
open CCM25Concrete.CompactLogConvolution
open Matrix

#print axioms classWindowFun_contDiff
#print axioms classWindowFun_support_subset_Icc
#print axioms classWindowFun_hasCompactSupport
#print axioms classWindowProduct_integrable
#print axioms classGramEntry
#print axioms classGramMatrix
#print axioms classGramMatrix_apply
#print axioms classWindowTest_apply
#print axioms classTestFamily_support
#print axioms classGramEntry_complex_integral
#print axioms classGramMatrix_transpose
#print axioms classGramMatrix_quadratic_eq_integral_square
#print axioms classGramMatrix_quadratic_nonneg
#print axioms hbox_of_classGramBounds

namespace ConnesWeilRH.Source.C1ClassGramOwner

noncomputable example : Matrix (Fin 8) (Fin 8) ℝ :=
  classGramMatrix 2 (by norm_num)

example (c : Fin 8 → ℝ) :
    0 ≤ c ⬝ᵥ (classGramMatrix 2 (by norm_num) *ᵥ c) :=
  classGramMatrix_quadratic_nonneg 2 (by norm_num) c

example (GLo GHi MLo MHi M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, GLo i j ≤ classGramMatrix 2 (by norm_num) i j ∧
      classGramMatrix 2 (by norm_num) i j ≤ GHi i j)
    (hM : ∀ i j, MLo i j ≤ M_true i j ∧ M_true i j ≤ MHi i j) :
    Hbox GLo GHi MLo MHi (classGramMatrix 2 (by norm_num)) M_true :=
  hbox_of_classGramBounds 2 (by norm_num) GLo GHi MLo MHi M_true hG hM

end ConnesWeilRH.Source.C1ClassGramOwner
