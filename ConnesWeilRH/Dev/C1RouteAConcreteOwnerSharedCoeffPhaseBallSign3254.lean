import ConnesWeilRH.Dev.C1RouteAConcreteOwnerSharedCoeffPhaseBall3253

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000

private theorem record2680_cell17168_shared_sum_chain3254
    {α : Type*} [AddCommMonoid α] (f : Fin 30 → α) :
    (∑ family ∈ record2680Cell17168SharedFamilies3247, f family) =
      f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 +
      f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 +
      f 24 + f 25 + f 26 + f 27 + f 28 + f 29 := by
  classical
  unfold record2680Cell17168SharedFamilies3247
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ] <;>
    ac_rfl

set_option maxHeartbeats 10000000 in
theorem record2680_cell17168_family8_coeff_phase_ball_upper3254 :
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

set_option maxHeartbeats 10000000 in
theorem record2680_cell17168_shared_coeff_phase_ball_sign3254 :
    record2680Cell17168SharedCoeffPhaseBall3253.center.re +
        record2680Cell17168SharedCoeffPhaseBall3253.radius < 0 := by
  change
    (∑ family ∈ record2680Cell17168SharedFamilies3247,
      (record2680Cell17168CoeffPhaseBall3253 family).center).re +
        ∑ family ∈ record2680Cell17168SharedFamilies3247,
          (record2680Cell17168CoeffPhaseBall3253 family).radius < 0
  rw [record2680_cell17168_shared_sum_chain3254,
    record2680_cell17168_shared_sum_chain3254]
  norm_num [record2680Cell17168SharedCoeffPhaseBall3253,
    record2680Cell17168SharedFamilies3247,
    record2680Cell17168CoeffPhaseBall3253,
    record2680MiddlePointPhaseBall3236,
    record2680MiddlePointPhaseBaseBall3236,
    ComplexTaxiBall3235.sumFinset,
    ComplexTaxiBall3235.mul,
    ComplexTaxiBall3235.point,
    taxiNorm3235,
    record2680CorrectionCoefficient,
    capturedModulations2584, record2680Center3212, record2680Grid3212,
    diagnosticRadius3201, Matrix.cons_val_zero, Matrix.cons_val_four,
    Matrix.cons_val_8, Matrix.cons_val_9, Matrix.cons_val_10,
    Matrix.cons_val_11, Matrix.cons_val_12, Matrix.cons_val_13,
    Matrix.cons_val_14, Matrix.cons_val_15, Matrix.cons_val_16,
    Matrix.cons_val_17, Matrix.cons_val_18, Matrix.cons_val_19,
    Matrix.cons_val_20, Matrix.cons_val_21, Matrix.cons_val_22,
    Matrix.cons_val_23, Matrix.cons_val_24, Matrix.cons_val_25,
    Matrix.cons_val_26, Matrix.cons_val_27, Matrix.cons_val_28,
    Matrix.cons_val_29, Fin.ext_iff, reExpIPartial2676, imExpIPartial2676,
    Finset.sum_range_succ, binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

end ConnesWeilRH.Dev
