import ConnesWeilRH.Dev.C1RouteAConcreteOwnerSharedBumpBlock3247

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell17168PhaseBlock0812Rect3249 : ComplexRect2427 :=
  (record2680Cell17168PhaseRect3247 8).add
    ((record2680Cell17168PhaseRect3247 9).add
      ((record2680Cell17168PhaseRect3247 10).add
        ((record2680Cell17168PhaseRect3247 11).add
          (record2680Cell17168PhaseRect3247 12))))

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
theorem record2680_cell17168_phase_block0812_reHi_bound3249 :
    record2680Cell17168PhaseBlock0812Rect3249.reHi ≤ 100000 := by
  norm_num [record2680Cell17168PhaseBlock0812Rect3249,
    record2680Cell17168PhaseRect3247, complexRectPowSq3218,
    phaseRect3218, phaseTaylorError3218, reExpIPartial2676,
    imExpIPartial2676, ComplexRect2427.add, ComplexRect2427.mul,
    RealInterval2429.mul, RealInterval2429.add, RealInterval2429.sub,
    record2680CorrectionCoefficient, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674, capturedModulations2584,
    record2680Center3212, record2680Grid3212, diagnosticRadius3201,
    Matrix.cons_val_zero, Matrix.cons_val_four, Fin.ext_iff]

end ConnesWeilRH.Dev
