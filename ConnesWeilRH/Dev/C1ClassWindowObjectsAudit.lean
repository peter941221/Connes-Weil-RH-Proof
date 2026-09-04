/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ClassWindowObjects

/-!
# Record 1124 audit: class window-test objects

Focused axiom audit for every public declaration introduced by
`C1ClassWindowObjects`, plus fidelity examples.  The record lands the
bridge objects; it certifies no number and does not claim RH.
-/

open ConnesWeilRH Source C1ClassWindowObjects

#print axioms classBump
#print axioms classBump_eq_exp
#print axioms classBump_eq_zero
#print axioms classBump_contDiff
#print axioms classBump_pos
#print axioms legendrePoly
#print axioms contDiff_legendreEval
#print axioms classWindowFun
#print axioms support_subset_Ioo
#print axioms support_subset_Icc
#print axioms classWindowTest
#print axioms classWindowTest_support
#print axioms classWindowTest_support_Icc
#print axioms classTestFamily

namespace ConnesWeilRH.Source.C1ClassWindowObjects

open MeasureTheory Set
open CCM25Concrete.CompactLogConvolution

/-- Fidelity: the window test at the (2, 8) class scale, index 3, is a
compact-log test supported in the open window. -/
example :
    ∃ w : CompactLogTest,
      Function.support w.test ⊆ Set.Ioo (-(2 : ℝ)) 2 :=
  ⟨classWindowTest 2 (by norm_num) 3, classWindowTest_support 2 (by norm_num) 3⟩

/-- Fidelity: the (4, 8) class family object. -/
noncomputable example : Fin 8 → CompactLogTest := classTestFamily 4 (by norm_num)

/-- Fidelity: the bump agrees with the pipeline formula inside the window. -/
example : classBump (1 / 2) = Real.exp (-(1 / (1 - (1 / 2) ^ 2))) :=
  classBump_eq_exp (by norm_num)

end ConnesWeilRH.Source.C1ClassWindowObjects
