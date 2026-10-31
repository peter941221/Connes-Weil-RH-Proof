import ConnesWeilRH.Dev.C1RouteAConcreteOwnerSharedBumpBlock3247

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell17168PhaseFamily10Box3250 : ComplexRect2427 :=
  { reLo := 19 / 100
    reHi := 21 / 100
    imLo := 97 / 100
    imHi := 99 / 100 }

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
theorem record2680_cell17168_phase_family10_box_subset3250 :
    record2680Cell17168PhaseFamily10Box3250.reLo ≤
        (complexRectPowSq3218
          (phaseRect3218
            (capturedModulations2584 10 * record2680Center3212 17168)) 9).reLo ∧
      (complexRectPowSq3218
          (phaseRect3218
            (capturedModulations2584 10 * record2680Center3212 17168)) 9).reHi ≤
        record2680Cell17168PhaseFamily10Box3250.reHi ∧
      record2680Cell17168PhaseFamily10Box3250.imLo ≤
        (complexRectPowSq3218
          (phaseRect3218
            (capturedModulations2584 10 * record2680Center3212 17168)) 9).imLo ∧
      (complexRectPowSq3218
          (phaseRect3218
            (capturedModulations2584 10 * record2680Center3212 17168)) 9).imHi ≤
        record2680Cell17168PhaseFamily10Box3250.imHi := by
  norm_num [record2680Cell17168PhaseFamily10Box3250,
    complexRectPowSq3218, phaseRect3218, phaseTaylorError3218,
    reExpIPartial2676, imExpIPartial2676, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four,
    Fin.ext_iff]

end ConnesWeilRH.Dev
