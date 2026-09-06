/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateMatrixBoxData

namespace ConnesWeilRH
namespace Source
namespace C1GateMatrixBoxDataAudit

open C1ClassWindowObjects
open C1GateMatrixRepresentation

#print axioms C1GateMatrixBoxData.zero_box_odd_data
#print axioms C1GateMatrixBoxData.gateMatrix_mem_zero_box_of_odd
#print axioms C1GateMatrixBoxData.q28_hboxM_of_sameParity

/-- The mixed-parity boxes hold for every class owner, by D1. -/
example (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    C1GateMatrixBoxData.MLo_q28M i j ≤
        gateMatrix (classTestFamily a ha) i j ∧
      gateMatrix (classTestFamily a ha) i j ≤
        C1GateMatrixBoxData.MHi_q28M i j :=
  C1GateMatrixBoxData.gateMatrix_mem_zero_box_of_odd a ha i j hodd

/-- Concrete mixed entry (0,1) at the pipeline radius a = 2. -/
example (a : ℝ) (ha : 0 < a) :
    C1GateMatrixBoxData.MLo_q28M 0 1 ≤
        gateMatrix (classTestFamily a ha) 0 1 ∧
      gateMatrix (classTestFamily a ha) 0 1 ≤
        C1GateMatrixBoxData.MHi_q28M 0 1 :=
  C1GateMatrixBoxData.gateMatrix_mem_zero_box_of_odd a ha 0 1 (by norm_num)

/-- The conditional D5 binding reads off the same-parity hypothesis. -/
example (a : ℝ) (ha : 0 < a)
    (hsp : ∀ i j : Fin 8, Even ((i : ℕ) + (j : ℕ)) →
      C1GateMatrixBoxData.MLo_q28M i j ≤
          gateMatrix (classTestFamily a ha) i j ∧
        gateMatrix (classTestFamily a ha) i j ≤
          C1GateMatrixBoxData.MHi_q28M i j) :
    ∀ i j : Fin 8, C1GateMatrixBoxData.MLo_q28M i j ≤
        gateMatrix (classTestFamily a ha) i j ∧
      gateMatrix (classTestFamily a ha) i j ≤
        C1GateMatrixBoxData.MHi_q28M i j :=
  C1GateMatrixBoxData.q28_hboxM_of_sameParity a ha hsp

end C1GateMatrixBoxDataAudit
end Source
end ConnesWeilRH
