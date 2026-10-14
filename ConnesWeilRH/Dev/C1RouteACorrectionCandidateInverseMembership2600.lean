import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectBounds2600Common

namespace ConnesWeilRH.Dev

/-! The 2600 payload uses point rectangles.  This definition selects the
stored lower endpoints as the concrete candidate inverse matrix; the
membership theorem below verifies that every selected coordinate is inside
its corresponding rectangle. -/

noncomputable def candidateInverseMatrix2600 :
    Matrix (Fin 30) (Fin 30) ℂ :=
  fun i j =>
    let r := candidateInverseInterval2600 i j
    ⟨r.reLo, r.imLo⟩

set_option maxHeartbeats 0 in
theorem candidateInverseInterval2600_mem_candidateInverseMatrix2600
    (i j : Fin 30) :
    (candidateInverseInterval2600 i j).Mem
      (candidateInverseMatrix2600 i j) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [candidateInverseMatrix2600, candidateInverseInterval2600,
      candidateInverseInterval2600_row_00,
      candidateInverseInterval2600_row_01,
      candidateInverseInterval2600_row_02,
      candidateInverseInterval2600_row_03,
      candidateInverseInterval2600_row_04,
      candidateInverseInterval2600_row_05,
      candidateInverseInterval2600_row_06,
      candidateInverseInterval2600_row_07,
      candidateInverseInterval2600_row_08,
      candidateInverseInterval2600_row_09,
      candidateInverseInterval2600_row_10,
      candidateInverseInterval2600_row_11,
      candidateInverseInterval2600_row_12,
      candidateInverseInterval2600_row_13,
      candidateInverseInterval2600_row_14,
      candidateInverseInterval2600_row_15,
      candidateInverseInterval2600_row_16,
      candidateInverseInterval2600_row_17,
      candidateInverseInterval2600_row_18,
      candidateInverseInterval2600_row_19,
      candidateInverseInterval2600_row_20,
      candidateInverseInterval2600_row_21,
      candidateInverseInterval2600_row_22,
      candidateInverseInterval2600_row_23,
      candidateInverseInterval2600_row_24,
      candidateInverseInterval2600_row_25,
      candidateInverseInterval2600_row_26,
      candidateInverseInterval2600_row_27,
      candidateInverseInterval2600_row_28,
      candidateInverseInterval2600_row_29]

#print axioms candidateInverseInterval2600_mem_candidateInverseMatrix2600

end ConnesWeilRH.Dev
