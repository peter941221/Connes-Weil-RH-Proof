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

private theorem lowerCorner_mem_of_degenerate_rect
    (r : ComplexRect2427)
    (hre : r.reHi = r.reLo)
    (him : r.imHi = r.imLo) :
    r.Mem ⟨r.reLo, r.imLo⟩ := by
  rw [ComplexRect2427.Mem]
  constructor
  · exact le_rfl
  constructor
  · simp [hre]
  constructor
  · exact le_rfl
  · simp [him]

set_option maxHeartbeats 0 in
theorem candidateInverseInterval2600_mem_candidateInverseMatrix2600
    (i j : Fin 30) :
    (candidateInverseInterval2600 i j).Mem
      (candidateInverseMatrix2600 i j) := by
  fin_cases i <;> fin_cases j <;>
    apply lowerCorner_mem_of_degenerate_rect <;> rfl

#print axioms candidateInverseInterval2600_mem_candidateInverseMatrix2600

end ConnesWeilRH.Dev
