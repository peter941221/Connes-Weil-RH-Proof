/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateMatrixParity

namespace ConnesWeilRH
namespace Source
namespace C1GateMatrixParityAudit

open C1ClassWindowObjects
open C1GateMatrixRepresentation

#print axioms C1GateMatrixParity.classPairTest_apply
#print axioms C1GateMatrixParity.classPairTest_neg
#print axioms C1GateMatrixParity.classPairTest_neg_of_odd
#print axioms C1GateMatrixParity.classPairTest_even_add_zero_of_odd
#print axioms C1GateMatrixParity.classPairTest_at_zero_of_odd
#print axioms C1GateMatrixParity.archimedeanTerm_classPairTest_zero_of_odd
#print axioms C1GateMatrixParity.finitePrimeSum_classPairTest_zero_of_odd
#print axioms C1GateMatrixParity.ICgate_classPairTest_zero_of_odd
#print axioms C1GateMatrixParity.gateMatrix_zero_of_odd

example (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    gateMatrix (classTestFamily a ha) i j = 0 :=
  C1GateMatrixParity.gateMatrix_zero_of_odd a ha i j hodd

example : gateMatrix (classTestFamily 2 (by norm_num)) 0 1 = 0 := by
  exact C1GateMatrixParity.gateMatrix_zero_of_odd 2 (by norm_num) 0 1
    (by norm_num)

end C1GateMatrixParityAudit
end Source
end ConnesWeilRH
