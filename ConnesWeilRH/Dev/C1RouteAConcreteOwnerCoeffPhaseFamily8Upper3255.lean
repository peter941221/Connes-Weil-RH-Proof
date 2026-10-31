import ConnesWeilRH.Dev.C1RouteAConcreteOwnerSharedCoeffPhaseBall3253

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000 in
theorem record2680_cell17168_family8_coeff_phase_ball_upper3255 :
    (record2680Cell17168CoeffPhaseBall3253 (8 : Fin 30)).center.re +
        (record2680Cell17168CoeffPhaseBall3253 (8 : Fin 30)).radius ≤ 10000 := by
  norm_num [record2680Cell17168CoeffPhaseBall3253,
    record2680MiddlePointPhaseBall3236,
    record2680MiddlePointPhaseBaseBall3236,
    ComplexTaxiBall3235.mul,
    ComplexTaxiBall3235.point,
    taxiNorm3235,
    record2680CorrectionCoefficient,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four,
    Matrix.cons_val_8, Fin.ext_iff, reExpIPartial2676, imExpIPartial2676,
    Finset.sum_range_succ, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev
