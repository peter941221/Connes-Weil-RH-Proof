import ConnesWeilRH.Dev.C1RouteASafeConstants2523

/-! Generated exact witnesses for record 2523. No external bound is assumed. -/
namespace ConnesWeilRH.Dev
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope
set_option linter.style.longLine false
set_option maxRecDepth 100000

theorem safeCell320Family0_2523 : safeFamily2523 320 0 ≤ ((182134233 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 0) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 320 0 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((182134233 : ℝ) / 1024)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell320Family1_2523 : safeFamily2523 320 1 ≤ ((30986855 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 1) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 320 1 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((30986855 : ℝ) / 1024)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell320Family2_2523 : safeFamily2523 320 2 ≤ ((27581823 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 2) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 320 2 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((27581823 : ℝ) / 1024)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell320Family3_2523 : safeFamily2523 320 3 ≤ ((1464917 : ℝ) / 64) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 3) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 320 3 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1464917 : ℝ) / 64)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell320Family4_2523 : safeFamily2523 320 4 ≤ ((687 : ℝ) / 16) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 4) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 320 4 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((687 : ℝ) / 16)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell320Family5_2523 : safeFamily2523 320 5 ≤ ((48393 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 5) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 320 5 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((48393 : ℝ) / 512)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell320Family6_2523 : safeFamily2523 320 6 ≤ ((11937 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 6) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 320 6 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((11937 : ℝ) / 256)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell320Family7_2523 : safeFamily2523 320 7 ≤ ((3905 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 7) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 320 7 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((3905 : ℝ) / 512)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell320Family8_2523 : safeFamily2523 320 8 ≤ ((1078783 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 8) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 320 8 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1078783 : ℝ) / 1024)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell320Family9_2523 : safeFamily2523 320 9 ≤ ((1027873 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 9) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 320 9 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1027873 : ℝ) / 512)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell320Family10_2523 : safeFamily2523 320 10 ≤ ((1824139 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 10) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 320 10 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1824139 : ℝ) / 1024)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell320Family11_2523 : safeFamily2523 320 11 ≤ ((1746739 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 11) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 320 11 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1746739 : ℝ) / 1024)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell320Family12_2523 : safeFamily2523 320 12 ≤ ((3261471 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 12) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 320 12 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((3261471 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell320Family13_2523 : safeFamily2523 320 13 ≤ ((1550793 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 13) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 320 13 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1550793 : ℝ) / 1024)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell320Family14_2523 : safeFamily2523 320 14 ≤ ((89376029 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 14) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 320 14 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((89376029 : ℝ) / 1024)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell320Family15_2523 : safeFamily2523 320 15 ≤ ((52794857 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 15) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 320 15 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((52794857 : ℝ) / 512)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell320Family16_2523 : safeFamily2523 320 16 ≤ ((1032637 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 16) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 320 16 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1032637 : ℝ) / 512)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell320Family17_2523 : safeFamily2523 320 17 ≤ ((3971667 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 17) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 320 17 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((3971667 : ℝ) / 512)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell320Family18_2523 : safeFamily2523 320 18 ≤ ((1483157 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 18) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 320 18 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((1483157 : ℝ) / 512)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell320Family19_2523 : safeFamily2523 320 19 ≤ ((4380101 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 19) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 320 19 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((4380101 : ℝ) / 512)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell320Family20_2523 : safeFamily2523 320 20 ≤ ((2355853 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 20) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 320 20 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((2355853 : ℝ) / 256)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell320Family21_2523 : safeFamily2523 320 21 ≤ ((2991701 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 21) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 320 21 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((2991701 : ℝ) / 1024)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell320Family22_2523 : safeFamily2523 320 22 ≤ ((11924521 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 22) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 320 22 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((11924521 : ℝ) / 1024)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell320Family23_2523 : safeFamily2523 320 23 ≤ ((13787745 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 23) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 320 23 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((13787745 : ℝ) / 1024)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell320Family24_2523 : safeFamily2523 320 24 ≤ ((3057447 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 24) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 320 24 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((3057447 : ℝ) / 1024)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell320Family25_2523 : safeFamily2523 320 25 ≤ ((15343999 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 25) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 320 25 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((15343999 : ℝ) / 1024)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell320Family26_2523 : safeFamily2523 320 26 ≤ ((10185611 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 26) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 320 26 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((10185611 : ℝ) / 1024)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell320Family27_2523 : safeFamily2523 320 27 ≤ ((5158949 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 27) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 320 27 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((5158949 : ℝ) / 128)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell320Family28_2523 : safeFamily2523 320 28 ≤ ((18048529 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 28) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 320 28 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((18048529 : ℝ) / 512)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell320Family29_2523 : safeFamily2523 320 29 ≤ ((42171715 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 320 29) ^ 2) = ((30 : ℝ) / 1) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 320 29 ≤ ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((30 : ℝ) / 1) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 320 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((1871524593768046887877252484585251993 : ℝ) / 20000000000000000000000000000000000000000000000000) ((42171715 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 320 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell320_2523 : (∑ i : Fin 30, safeFamily2523 320 i) ≤ ((339405617 : ℝ) / 512) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell320Family0_2523 (add_le_add safeCell320Family1_2523 (add_le_add safeCell320Family2_2523 (add_le_add safeCell320Family3_2523 (add_le_add safeCell320Family4_2523 (add_le_add safeCell320Family5_2523 (add_le_add safeCell320Family6_2523 (add_le_add safeCell320Family7_2523 (add_le_add safeCell320Family8_2523 (add_le_add safeCell320Family9_2523 (add_le_add safeCell320Family10_2523 (add_le_add safeCell320Family11_2523 (add_le_add safeCell320Family12_2523 (add_le_add safeCell320Family13_2523 (add_le_add safeCell320Family14_2523 (add_le_add safeCell320Family15_2523 (add_le_add safeCell320Family16_2523 (add_le_add safeCell320Family17_2523 (add_le_add safeCell320Family18_2523 (add_le_add safeCell320Family19_2523 (add_le_add safeCell320Family20_2523 (add_le_add safeCell320Family21_2523 (add_le_add safeCell320Family22_2523 (add_le_add safeCell320Family23_2523 (add_le_add safeCell320Family24_2523 (add_le_add safeCell320Family25_2523 (add_le_add safeCell320Family26_2523 (add_le_add safeCell320Family27_2523 (add_le_add safeCell320Family28_2523 (safeCell320Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell321Family0_2523 : safeFamily2523 321 0 ≤ ((183488607 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 0) ^ 2) = ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8569787734512104032451264000262961787331326820188784875410399444857024027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 321 0 ≤ ((933967242139752358929678507909268233 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8569787734512104032451264000262961787331326820188784875410399444857024027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((933967242139752358929678507909268233 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((933967242139752358929678507909268233 : ℝ) / 10000000000000000000000000000000000000000000000000) ((183488607 : ℝ) / 1024)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell321Family1_2523 : safeFamily2523 321 1 ≤ ((15559591 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 1) ^ 2) = ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10978288432553822719049635587169219639900167846849227966107636556232161) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 321 1 ≤ ((730262167723424042240191555441003 : ℝ) / 7812500000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10978288432553822719049635587169219639900167846849227966107636556232161) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((730262167723424042240191555441003 : ℝ) / 7812500000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((730262167723424042240191555441003 : ℝ) / 7812500000000000000000000000000000000000000000) ((15559591 : ℝ) / 512)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell321Family2_2523 : safeFamily2523 321 2 ≤ ((13827059 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 2) ^ 2) = ((8605454527890192662077563950501996964407315123001107474716557312011718750 : ℝ) / 286842056510633226677422552384533821155451269110523778899443528893855201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 321 2 ≤ ((9351334323013680171192423702747446907 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((8605454527890192662077563950501996964407315123001107474716557312011718750 : ℝ) / 286842056510633226677422552384533821155451269110523778899443528893855201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9351334323013680171192423702747446907 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((9351334323013680171192423702747446907 : ℝ) / 100000000000000000000000000000000000000000000000000) ((13827059 : ℝ) / 512)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell321Family3_2523 : safeFamily2523 321 3 ≤ ((1467401 : ℝ) / 64) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 3) ^ 2) = ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37884676394515573586340499032572839943494239082546495474209112823763274027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 321 3 ≤ ((4676779704076453402946769999231028633 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37884676394515573586340499032572839943494239082546495474209112823763274027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4676779704076453402946769999231028633 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((4676779704076453402946769999231028633 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1467401 : ℝ) / 64)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell321Family4_2523 : safeFamily2523 321 4 ≤ ((22009 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 4) ^ 2) = ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 658195395176109732995731159540244571335246735093234217024028489831355201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 321 4 ≤ ((146170028944281947501302575730156761 : ℝ) / 1562500000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 658195395176109732995731159540244571335246735093234217024028489831355201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((146170028944281947501302575730156761 : ℝ) / 1562500000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((146170028944281947501302575730156761 : ℝ) / 1562500000000000000000000000000000000000000000000) ((22009 : ℝ) / 512)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell321Family5_2523 : safeFamily2523 321 5 ≤ ((24865 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 5) ^ 2) = ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31250246273945742653426054602457159227855455205951750757987338471289822081) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 321 5 ≤ ((583928291455089767138943337912816663 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31250246273945742653426054602457159227855455205951750757987338471289822081) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((583928291455089767138943337912816663 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((583928291455089767138943337912816663 : ℝ) / 6250000000000000000000000000000000000000000000000) ((24865 : ℝ) / 256)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell321Family6_2523 : safeFamily2523 321 6 ≤ ((12209 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 6) ^ 2) = ((1638400000000000000000 : ℝ) / 54611901677524309333) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 321 6 ≤ ((935026653467137087150599903954014339 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1638400000000000000000 : ℝ) / 54611901677524309333) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((935026653467137087150599903954014339 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((935026653467137087150599903954014339 : ℝ) / 10000000000000000000000000000000000000000000000000) ((12209 : ℝ) / 256)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell321Family7_2523 : safeFamily2523 321 7 ≤ ((7967 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 7) ^ 2) = ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37884676394515573586340499032572839943494239082546495474209112823763274027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 321 7 ≤ ((4676779704076453402946769999231028633 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37884676394515573586340499032572839943494239082546495474209112823763274027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4676779704076453402946769999231028633 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((4676779704076453402946769999231028633 : ℝ) / 50000000000000000000000000000000000000000000000000) ((7967 : ℝ) / 1024)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell321Family8_2523 : safeFamily2523 321 8 ≤ ((1095653 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 8) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 321 8 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1095653 : ℝ) / 1024)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell321Family9_2523 : safeFamily2523 321 9 ≤ ((2077127 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 9) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 321 9 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((2077127 : ℝ) / 1024)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell321Family10_2523 : safeFamily2523 321 10 ≤ ((1839845 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 10) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 321 10 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1839845 : ℝ) / 1024)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell321Family11_2523 : safeFamily2523 321 11 ≤ ((440043 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 11) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 321 11 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((440043 : ℝ) / 256)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell321Family12_2523 : safeFamily2523 321 12 ≤ ((1641989 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 12) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 321 12 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1641989 : ℝ) / 512)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell321Family13_2523 : safeFamily2523 321 13 ≤ ((1560551 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 13) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 321 13 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1560551 : ℝ) / 1024)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell321Family14_2523 : safeFamily2523 321 14 ≤ ((44928131 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 14) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 321 14 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((44928131 : ℝ) / 512)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell321Family15_2523 : safeFamily2523 321 15 ≤ ((53050385 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 15) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 321 15 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((53050385 : ℝ) / 512)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell321Family16_2523 : safeFamily2523 321 16 ≤ ((2074577 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 16) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 321 16 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((2074577 : ℝ) / 1024)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell321Family17_2523 : safeFamily2523 321 17 ≤ ((3987345 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 17) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 321 17 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((3987345 : ℝ) / 512)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell321Family18_2523 : safeFamily2523 321 18 ≤ ((1488739 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 18) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 321 18 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1488739 : ℝ) / 512)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell321Family19_2523 : safeFamily2523 321 19 ≤ ((17169 : ℝ) / 2) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 19) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 321 19 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((17169 : ℝ) / 2)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell321Family20_2523 : safeFamily2523 321 20 ≤ ((4726651 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 20) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 321 20 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((4726651 : ℝ) / 512)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell321Family21_2523 : safeFamily2523 321 21 ≤ ((3000543 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 21) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 321 21 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((3000543 : ℝ) / 1024)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell321Family22_2523 : safeFamily2523 321 22 ≤ ((5979269 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 22) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 321 22 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((5979269 : ℝ) / 512)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell321Family23_2523 : safeFamily2523 321 23 ≤ ((6911673 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 23) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 321 23 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((6911673 : ℝ) / 512)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell321Family24_2523 : safeFamily2523 321 24 ≤ ((766249 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 24) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 321 24 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((766249 : ℝ) / 256)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell321Family25_2523 : safeFamily2523 321 25 ≤ ((15379849 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 25) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 321 25 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((15379849 : ℝ) / 1024)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell321Family26_2523 : safeFamily2523 321 26 ≤ ((5104061 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 26) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 321 26 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((5104061 : ℝ) / 512)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell321Family27_2523 : safeFamily2523 321 27 ≤ ((10338973 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 27) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 321 27 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((10338973 : ℝ) / 256)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell321Family28_2523 : safeFamily2523 321 28 ≤ ((18084275 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 28) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 321 28 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((18084275 : ℝ) / 512)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell321Family29_2523 : safeFamily2523 321 29 ≤ ((10562859 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 321 29) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 321 29 ≤ ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12547280781661961444986958800940122890150067064887479729509789093294524027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 321 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9345359021310834481066795115971715547 : ℝ) / 100000000000000000000000000000000000000000000000000) ((10562859 : ℝ) / 256)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 321 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell321_2523 : (∑ i : Fin 30, safeFamily2523 321 i) ≤ ((681996809 : ℝ) / 1024) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell321Family0_2523 (add_le_add safeCell321Family1_2523 (add_le_add safeCell321Family2_2523 (add_le_add safeCell321Family3_2523 (add_le_add safeCell321Family4_2523 (add_le_add safeCell321Family5_2523 (add_le_add safeCell321Family6_2523 (add_le_add safeCell321Family7_2523 (add_le_add safeCell321Family8_2523 (add_le_add safeCell321Family9_2523 (add_le_add safeCell321Family10_2523 (add_le_add safeCell321Family11_2523 (add_le_add safeCell321Family12_2523 (add_le_add safeCell321Family13_2523 (add_le_add safeCell321Family14_2523 (add_le_add safeCell321Family15_2523 (add_le_add safeCell321Family16_2523 (add_le_add safeCell321Family17_2523 (add_le_add safeCell321Family18_2523 (add_le_add safeCell321Family19_2523 (add_le_add safeCell321Family20_2523 (add_le_add safeCell321Family21_2523 (add_le_add safeCell321Family22_2523 (add_le_add safeCell321Family23_2523 (add_le_add safeCell321Family24_2523 (add_le_add safeCell321Family25_2523 (add_le_add safeCell321Family26_2523 (add_le_add safeCell321Family27_2523 (add_le_add safeCell321Family28_2523 (safeCell321Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell322Family0_2523 : safeFamily2523 322 0 ≤ ((92069867 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 0) ^ 2) = ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8568142229904566012142891699753245906851095996206755156086653779183955483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 322 0 ≤ ((4643006711465880411023509923870011633 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8568142229904566012142891699753245906851095996206755156086653779183955483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4643006711465880411023509923870011633 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((4643006711465880411023509923870011633 : ℝ) / 50000000000000000000000000000000000000000000000000) ((92069867 : ℝ) / 512)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell322Family1_2523 : safeFamily2523 322 1 ≤ ((15591631 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 1) ^ 2) = ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10977083228983848583081589468631830079001561286315514792774815023756769) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 322 1 ≤ ((1863323426229358140147767400940890599 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10977083228983848583081589468631830079001561286315514792774815023756769) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1863323426229358140147767400940890599 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((1863323426229358140147767400940890599 : ℝ) / 20000000000000000000000000000000000000000000000000) ((15591631 : ℝ) / 512)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell322Family2_2523 : safeFamily2523 322 2 ≤ ((27689257 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 2) ^ 2) = ((8605454527890192662077563950501996964407315123001107474716557312011718750 : ℝ) / 286822773253513640501933814487935588181073564141984368126118384374248929) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 322 2 ≤ ((9332492044116298304535588217205359603 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((8605454527890192662077563950501996964407315123001107474716557312011718750 : ℝ) / 286822773253513640501933814487935588181073564141984368126118384374248929) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9332492044116298304535588217205359603 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((9332492044116298304535588217205359603 : ℝ) / 100000000000000000000000000000000000000000000000000) ((27689257 : ℝ) / 1024)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell322Family3_2523 : safeFamily2523 322 3 ≤ ((11748887 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 3) ^ 2) = ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37883030889908035566032126732063124063014008258564465754885367158090205483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 322 3 ≤ ((4670689302856482541130766985505587049 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37883030889908035566032126732063124063014008258564465754885367158090205483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4670689302856482541130766985505587049 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((4670689302856482541130766985505587049 : ℝ) / 50000000000000000000000000000000000000000000000000) ((11748887 : ℝ) / 512)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell322Family4_2523 : safeFamily2523 322 4 ≤ ((44043 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 4) ^ 2) = ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 658176111918990146820242421643646338360869030124694806250703345311748929) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 322 4 ≤ ((9346662999076935383489872151979063179 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 658176111918990146820242421643646338360869030124694806250703345311748929) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9346662999076935383489872151979063179 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((9346662999076935383489872151979063179 : ℝ) / 100000000000000000000000000000000000000000000000000) ((44043 : ℝ) / 1024)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell322Family5_2523 : safeFamily2523 322 5 ≤ ((51221 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 5) ^ 2) = ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31245309760123128592500937700928011586414762734005661600016101474270616449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 322 5 ≤ ((2324668049870349374580219312896862673 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31245309760123128592500937700928011586414762734005661600016101474270616449) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2324668049870349374580219312896862673 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((2324668049870349374580219312896862673 : ℝ) / 25000000000000000000000000000000000000000000000000) ((51221 : ℝ) / 512)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell322Family6_2523 : safeFamily2523 322 6 ≤ ((49995 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 6) ^ 2) = ((409600000000000000000 : ℝ) / 13651901677524309333) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 322 6 ≤ ((4664114802621935370888589358731487299 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((409600000000000000000 : ℝ) / 13651901677524309333) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4664114802621935370888589358731487299 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((4664114802621935370888589358731487299 : ℝ) / 50000000000000000000000000000000000000000000000000) ((49995 : ℝ) / 1024)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell322Family7_2523 : safeFamily2523 322 7 ≤ ((8129 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 7) ^ 2) = ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37883030889908035566032126732063124063014008258564465754885367158090205483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 322 7 ≤ ((4670689302856482541130766985505587049 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37883030889908035566032126732063124063014008258564465754885367158090205483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4670689302856482541130766985505587049 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((4670689302856482541130766985505587049 : ℝ) / 50000000000000000000000000000000000000000000000000) ((8129 : ℝ) / 1024)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell322Family8_2523 : safeFamily2523 322 8 ≤ ((1109755 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 8) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 322 8 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((1109755 : ℝ) / 1024)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell322Family9_2523 : safeFamily2523 322 9 ≤ ((523283 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 9) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 322 9 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((523283 : ℝ) / 256)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell322Family10_2523 : safeFamily2523 322 10 ≤ ((462691 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 10) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 322 10 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((462691 : ℝ) / 256)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell322Family11_2523 : safeFamily2523 322 11 ≤ ((884507 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 11) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 322 11 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((884507 : ℝ) / 512)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell322Family12_2523 : safeFamily2523 322 12 ≤ ((3297905 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 12) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 322 12 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((3297905 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell322Family13_2523 : safeFamily2523 322 13 ≤ ((391557 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 13) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 322 13 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((391557 : ℝ) / 256)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell322Family14_2523 : safeFamily2523 322 14 ≤ ((45050605 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 14) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 322 14 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((45050605 : ℝ) / 512)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell322Family15_2523 : safeFamily2523 322 15 ≤ ((106333845 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 15) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 322 15 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((106333845 : ℝ) / 1024)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell322Family16_2523 : safeFamily2523 322 16 ≤ ((2078443 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 16) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 322 16 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((2078443 : ℝ) / 1024)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell322Family17_2523 : safeFamily2523 322 17 ≤ ((7985137 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 17) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 322 17 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((7985137 : ℝ) / 1024)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell322Family18_2523 : safeFamily2523 322 18 ≤ ((1490417 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 18) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 322 18 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((1490417 : ℝ) / 512)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell322Family19_2523 : safeFamily2523 322 19 ≤ ((8797801 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 19) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 322 19 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((8797801 : ℝ) / 1024)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell322Family20_2523 : safeFamily2523 322 20 ≤ ((4729199 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 20) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 322 20 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((4729199 : ℝ) / 512)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell322Family21_2523 : safeFamily2523 322 21 ≤ ((3001515 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 21) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 322 21 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((3001515 : ℝ) / 1024)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell322Family22_2523 : safeFamily2523 322 22 ≤ ((11961189 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 22) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 322 22 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((11961189 : ℝ) / 1024)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell322Family23_2523 : safeFamily2523 322 23 ≤ ((431959 : ℝ) / 32) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 23) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 322 23 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((431959 : ℝ) / 32)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell322Family24_2523 : safeFamily2523 322 24 ≤ ((1532253 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 24) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 322 24 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((1532253 : ℝ) / 512)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell322Family25_2523 : safeFamily2523 322 25 ≤ ((15375359 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 25) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 322 25 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((15375359 : ℝ) / 1024)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell322Family26_2523 : safeFamily2523 322 26 ≤ ((10203859 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 26) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 322 26 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((10203859 : ℝ) / 1024)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell322Family27_2523 : safeFamily2523 322 27 ≤ ((41331721 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 27) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 322 27 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((41331721 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell322Family28_2523 : safeFamily2523 322 28 ≤ ((18072589 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 28) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 322 28 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((18072589 : ℝ) / 512)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell322Family29_2523 : safeFamily2523 322 29 ≤ ((42220341 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 322 29) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 322 29 ≤ ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12545635277054423424678586500430407009669836240905450010186043427621455483) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 322 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((2327164281825145461460198705933865121 : ℝ) / 25000000000000000000000000000000000000000000000000) ((42220341 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 322 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell322_2523 : (∑ i : Fin 30, safeFamily2523 322 i) ≤ ((341631729 : ℝ) / 512) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell322Family0_2523 (add_le_add safeCell322Family1_2523 (add_le_add safeCell322Family2_2523 (add_le_add safeCell322Family3_2523 (add_le_add safeCell322Family4_2523 (add_le_add safeCell322Family5_2523 (add_le_add safeCell322Family6_2523 (add_le_add safeCell322Family7_2523 (add_le_add safeCell322Family8_2523 (add_le_add safeCell322Family9_2523 (add_le_add safeCell322Family10_2523 (add_le_add safeCell322Family11_2523 (add_le_add safeCell322Family12_2523 (add_le_add safeCell322Family13_2523 (add_le_add safeCell322Family14_2523 (add_le_add safeCell322Family15_2523 (add_le_add safeCell322Family16_2523 (add_le_add safeCell322Family17_2523 (add_le_add safeCell322Family18_2523 (add_le_add safeCell322Family19_2523 (add_le_add safeCell322Family20_2523 (add_le_add safeCell322Family21_2523 (add_le_add safeCell322Family22_2523 (add_le_add safeCell322Family23_2523 (add_le_add safeCell322Family24_2523 (add_le_add safeCell322Family25_2523 (add_le_add safeCell322Family26_2523 (add_le_add safeCell322Family27_2523 (add_le_add safeCell322Family28_2523 (safeCell322Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell323Family0_2523 : safeFamily2523 323 0 ≤ ((184080599 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 0) ^ 2) = ((771330261244315503529864929038958037274226338536451530366648320007324218750 : ℝ) / 25696199166676007934886813596711158318152133868710116871641233009186523729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 323 0 ≤ ((9197220716409070095840722774056902273 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((771330261244315503529864929038958037274226338536451530366648320007324218750 : ℝ) / 25696199166676007934886813596711158318152133868710116871641233009186523729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9197220716409070095840722774056902273 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((9197220716409070095840722774056902273 : ℝ) / 100000000000000000000000000000000000000000000000000) ((184080599 : ℝ) / 1024)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell323Family1_2523 : safeFamily2523 323 1 ≤ ((7794675 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 1) ^ 2) = ((36595633890257158103463280977827831645110122334534885635173034667968750 : ℝ) / 1219452728485247224792760659748464534537468557639925130061493978107161) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 323 1 ≤ ((9265595675049688053421086842893541663 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((36595633890257158103463280977827831645110122334534885635173034667968750 : ℝ) / 1219452728485247224792760659748464534537468557639925130061493978107161) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9265595675049688053421086842893541663 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((9265595675049688053421086842893541663 : ℝ) / 100000000000000000000000000000000000000000000000000) ((7794675 : ℝ) / 256)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell323Family2_2523 : safeFamily2523 323 2 ≤ ((13843555 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 2) ^ 2) = ((956161614210021406897507105611332996045257235889011941635173034667968750 : ℝ) / 31865626054627518171420657554845022210049339540120594463397386315730201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 323 2 ≤ ((9301166970558777348710660273778974691 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((956161614210021406897507105611332996045257235889011941635173034667968750 : ℝ) / 31865626054627518171420657554845022210049339540120594463397386315730201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9301166970558777348710660273778974691 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((9301166970558777348710660273778974691 : ℝ) / 100000000000000000000000000000000000000000000000000) ((13843555 : ℝ) / 512)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell323Family3_2523 : safeFamily2523 323 3 ≤ ((5874175 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 3) ^ 2) = ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113640865146686416596554518693640792786640870655783248668037373145905273729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 323 3 ≤ ((2330277540830136737637255452320727683 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113640865146686416596554518693640792786640870655783248668037373145905273729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2330277540830136737637255452320727683 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((2330277540830136737637255452320727683 : ℝ) / 25000000000000000000000000000000000000000000000000) ((5874175 : ℝ) / 256)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell323Family4_2523 : safeFamily2523 323 4 ≤ ((44041 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 4) ^ 2) = ((2194006076428276427958535796130368829977908789164713402050456237792968750 : ℝ) / 73127108128569352206788280572146216674471057982643976477240159753230201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 323 4 ≤ ((2333244971243454317095585320957442069 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((2194006076428276427958535796130368829977908789164713402050456237792968750 : ℝ) / 73127108128569352206788280572146216674471057982643976477240159753230201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2333244971243454317095585320957442069 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((2333244971243454317095585320957442069 : ℝ) / 25000000000000000000000000000000000000000000000000) ((44041 : ℝ) / 1024)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell323Family5_2523 : safeFamily2523 323 5 ≤ ((52849 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 5) ^ 2) = ((104172972595177602245781423009889583694452286766445934924370280456542968750 : ℝ) / 3470786915231715387884341799819936909334845401566168111488597016211697081) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 323 5 ≤ ((9225471158849567454811199348011187951 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((104172972595177602245781423009889583694452286766445934924370280456542968750 : ℝ) / 3470786915231715387884341799819936909334845401566168111488597016211697081) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9225471158849567454811199348011187951 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((9225471158849567454811199348011187951 : ℝ) / 100000000000000000000000000000000000000000000000000) ((52849 : ℝ) / 512)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell323Family6_2523 : safeFamily2523 323 6 ≤ ((51221 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 6) ^ 2) = ((4915200000000000000000 : ℝ) / 163801345293156351991) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 323 6 ≤ ((2322902269996249393949864031348307469 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((4915200000000000000000 : ℝ) / 163801345293156351991) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2322902269996249393949864031348307469 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((2322902269996249393949864031348307469 : ℝ) / 25000000000000000000000000000000000000000000000000) ((51221 : ℝ) / 1024)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell323Family7_2523 : safeFamily2523 323 7 ≤ ((1037 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 7) ^ 2) = ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113640865146686416596554518693640792786640870655783248668037373145905273729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 323 7 ≤ ((2330277540830136737637255452320727683 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113640865146686416596554518693640792786640870655783248668037373145905273729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2330277540830136737637255452320727683 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((2330277540830136737637255452320727683 : ℝ) / 25000000000000000000000000000000000000000000000000) ((1037 : ℝ) / 128)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell323Family8_2523 : safeFamily2523 323 8 ≤ ((140123 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 8) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 323 8 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((140123 : ℝ) / 128)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell323Family9_2523 : safeFamily2523 323 9 ≤ ((2103641 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 9) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 323 9 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((2103641 : ℝ) / 1024)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell323Family10_2523 : safeFamily2523 323 10 ≤ ((1856813 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 10) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 323 10 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1856813 : ℝ) / 1024)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell323Family11_2523 : safeFamily2523 323 11 ≤ ((1773201 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 11) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 323 11 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1773201 : ℝ) / 1024)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell323Family12_2523 : safeFamily2523 323 12 ≤ ((3303151 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 12) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 323 12 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((3303151 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell323Family13_2523 : safeFamily2523 323 13 ≤ ((1567781 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 13) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 323 13 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1567781 : ℝ) / 1024)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell323Family14_2523 : safeFamily2523 323 14 ≤ ((90109071 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 14) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 323 14 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((90109071 : ℝ) / 1024)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell323Family15_2523 : safeFamily2523 323 15 ≤ ((13285903 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 15) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 323 15 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((13285903 : ℝ) / 128)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell323Family16_2523 : safeFamily2523 323 16 ≤ ((519211 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 16) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 323 16 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((519211 : ℝ) / 256)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell323Family17_2523 : safeFamily2523 323 17 ≤ ((7974599 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 17) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 323 17 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((7974599 : ℝ) / 1024)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell323Family18_2523 : safeFamily2523 323 18 ≤ ((2976359 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 18) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 323 18 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((2976359 : ℝ) / 1024)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell323Family19_2523 : safeFamily2523 323 19 ≤ ((548873 : ℝ) / 64) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 19) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 323 19 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((548873 : ℝ) / 64)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell323Family20_2523 : safeFamily2523 323 20 ≤ ((1179833 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 20) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 323 20 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1179833 : ℝ) / 128)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell323Family21_2523 : safeFamily2523 323 21 ≤ ((1497305 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 21) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 323 21 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1497305 : ℝ) / 512)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell323Family22_2523 : safeFamily2523 323 22 ≤ ((5966227 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 22) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 323 22 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((5966227 : ℝ) / 512)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell323Family23_2523 : safeFamily2523 323 23 ≤ ((13785777 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 23) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 323 23 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((13785777 : ℝ) / 1024)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell323Family24_2523 : safeFamily2523 323 24 ≤ ((763995 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 24) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 323 24 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((763995 : ℝ) / 256)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell323Family25_2523 : safeFamily2523 323 25 ≤ ((15330561 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 25) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 323 25 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((15330561 : ℝ) / 1024)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell323Family26_2523 : safeFamily2523 323 26 ≤ ((2543213 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 26) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 323 26 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((2543213 : ℝ) / 256)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell323Family27_2523 : safeFamily2523 323 27 ≤ ((41199257 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 27) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 323 27 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((41199257 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell323Family28_2523 : safeFamily2523 323 28 ≤ ((36027113 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 28) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 323 28 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((36027113 : ℝ) / 1024)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell323Family29_2523 : safeFamily2523 323 29 ≤ ((42078659 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 323 29) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 323 29 ≤ ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37628678308125580172493897998742641626608354602806201433939401954499023729) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 323 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4623893057417467809258924243565583173 : ℝ) / 50000000000000000000000000000000000000000000000000) ((42078659 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 323 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell323_2523 : (∑ i : Fin 30, safeFamily2523 323 i) ≤ ((85324991 : ℝ) / 128) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell323Family0_2523 (add_le_add safeCell323Family1_2523 (add_le_add safeCell323Family2_2523 (add_le_add safeCell323Family3_2523 (add_le_add safeCell323Family4_2523 (add_le_add safeCell323Family5_2523 (add_le_add safeCell323Family6_2523 (add_le_add safeCell323Family7_2523 (add_le_add safeCell323Family8_2523 (add_le_add safeCell323Family9_2523 (add_le_add safeCell323Family10_2523 (add_le_add safeCell323Family11_2523 (add_le_add safeCell323Family12_2523 (add_le_add safeCell323Family13_2523 (add_le_add safeCell323Family14_2523 (add_le_add safeCell323Family15_2523 (add_le_add safeCell323Family16_2523 (add_le_add safeCell323Family17_2523 (add_le_add safeCell323Family18_2523 (add_le_add safeCell323Family19_2523 (add_le_add safeCell323Family20_2523 (add_le_add safeCell323Family21_2523 (add_le_add safeCell323Family22_2523 (add_le_add safeCell323Family23_2523 (add_le_add safeCell323Family24_2523 (add_le_add safeCell323Family25_2523 (add_le_add safeCell323Family26_2523 (add_le_add safeCell323Family27_2523 (add_le_add safeCell323Family28_2523 (safeCell323Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell324Family0_2523 : safeFamily2523 324 0 ≤ ((91655919 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 0) ^ 2) = ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8561560211474413930909402497714382384930172700278636278791671116491681307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 324 0 ≤ ((9074241645744670119260230233874151429 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8561560211474413930909402497714382384930172700278636278791671116491681307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9074241645744670119260230233874151429 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((9074241645744670119260230233874151429 : ℝ) / 100000000000000000000000000000000000000000000000000) ((91655919 : ℝ) / 512)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell324Family1_2523 : safeFamily2523 324 1 ≤ ((15552763 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 1) ^ 2) = ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10972262414703952039209404994482271835407135044180662099443528893855201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 324 1 ≤ ((9194603650290761205051992239756161599 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10972262414703952039209404994482271835407135044180662099443528893855201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9194603650290761205051992239756161599 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((9194603650290761205051992239756161599 : ℝ) / 100000000000000000000000000000000000000000000000000) ((15552763 : ℝ) / 512)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell324Family2_2523 : safeFamily2523 324 2 ≤ ((27647683 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 2) ^ 2) = ((8605454527890192662077563950501996964407315123001107474716557312011718750 : ℝ) / 286745640225035295799978862901542656283562744267826725032817806295823841) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 324 2 ≤ ((9257476709594754799108819034111190079 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((8605454527890192662077563950501996964407315123001107474716557312011718750 : ℝ) / 286745640225035295799978862901542656283562744267826725032817806295823841) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9257476709594754799108819034111190079 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((9257476709594754799108819034111190079 : ℝ) / 100000000000000000000000000000000000000000000000000) ((27647683 : ℝ) / 1024)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell324Family3_2523 : safeFamily2523 324 3 ≤ ((11737597 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 3) ^ 2) = ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37876448871477883484798637530024260541093084962636346877590384495397931307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 324 3 ≤ ((4646401646967191718235564666421925463 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37876448871477883484798637530024260541093084962636346877590384495397931307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4646401646967191718235564666421925463 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((4646401646967191718235564666421925463 : ℝ) / 50000000000000000000000000000000000000000000000000) ((11737597 : ℝ) / 512)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell324Family4_2523 : safeFamily2523 324 4 ≤ ((22007 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 4) ^ 2) = ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 658098978890511802118287470057253406463358210250537163157402767233323841) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 324 4 ≤ ((2328463733142901054077337425845413661 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 658098978890511802118287470057253406463358210250537163157402767233323841) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2328463733142901054077337425845413661 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((2328463733142901054077337425845413661 : ℝ) / 25000000000000000000000000000000000000000000000000) ((22007 : ℝ) / 512)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell324Family5_2523 : safeFamily2523 324 5 ≤ ((109189 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 5) ^ 2) = ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31225563704832672348800470094811421020651992846221304968131153486193793921) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 324 5 ≤ ((4561946475366501106987060559075380803 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31225563704832672348800470094811421020651992846221304968131153486193793921) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4561946475366501106987060559075380803 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((4561946475366501106987060559075380803 : ℝ) / 50000000000000000000000000000000000000000000000000) ((109189 : ℝ) / 1024)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell324Family6_2523 : safeFamily2523 324 6 ≤ ((52507 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 6) ^ 2) = ((102400000000000000000 : ℝ) / 3411901677524309333) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 324 6 ≤ ((4620282863577645461014765566293694383 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((102400000000000000000 : ℝ) / 3411901677524309333) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4620282863577645461014765566293694383 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((4620282863577645461014765566293694383 : ℝ) / 50000000000000000000000000000000000000000000000000) ((52507 : ℝ) / 1024)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell324Family7_2523 : safeFamily2523 324 7 ≤ ((8469 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 7) ^ 2) = ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37876448871477883484798637530024260541093084962636346877590384495397931307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 324 7 ≤ ((4646401646967191718235564666421925463 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1136556746881542587793298693982282357109629480716215161419510841369628906250 : ℝ) / 37876448871477883484798637530024260541093084962636346877590384495397931307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4646401646967191718235564666421925463 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((4646401646967191718235564666421925463 : ℝ) / 50000000000000000000000000000000000000000000000000) ((8469 : ℝ) / 1024)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell324Family8_2523 : safeFamily2523 324 8 ≤ ((141157 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 8) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 324 8 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((141157 : ℝ) / 128)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell324Family9_2523 : safeFamily2523 324 9 ≤ ((1054289 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 9) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 324 9 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((1054289 : ℝ) / 512)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell324Family10_2523 : safeFamily2523 324 10 ≤ ((928975 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 10) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 324 10 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((928975 : ℝ) / 512)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell324Family11_2523 : safeFamily2523 324 11 ≤ ((443175 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 11) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 324 11 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((443175 : ℝ) / 256)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell324Family12_2523 : safeFamily2523 324 12 ≤ ((3299677 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 12) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 324 12 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((3299677 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell324Family13_2523 : safeFamily2523 324 13 ≤ ((1565201 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 13) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 324 13 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((1565201 : ℝ) / 1024)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell324Family14_2523 : safeFamily2523 324 14 ≤ ((22469947 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 14) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 324 14 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((22469947 : ℝ) / 256)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell324Family15_2523 : safeFamily2523 324 15 ≤ ((105961249 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 15) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 324 15 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((105961249 : ℝ) / 1024)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell324Family16_2523 : safeFamily2523 324 16 ≤ ((2069791 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 16) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 324 16 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((2069791 : ℝ) / 1024)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell324Family17_2523 : safeFamily2523 324 17 ≤ ((3971577 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 17) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 324 17 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((3971577 : ℝ) / 512)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell324Family18_2523 : safeFamily2523 324 18 ≤ ((741021 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 18) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 324 18 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((741021 : ℝ) / 256)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell324Family19_2523 : safeFamily2523 324 19 ≤ ((8743145 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 19) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 324 19 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((8743145 : ℝ) / 1024)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell324Family20_2523 : safeFamily2523 324 20 ≤ ((9394243 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 20) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 324 20 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((9394243 : ℝ) / 1024)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell324Family21_2523 : safeFamily2523 324 21 ≤ ((1489939 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 21) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 324 21 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((1489939 : ℝ) / 512)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell324Family22_2523 : safeFamily2523 324 22 ≤ ((371017 : ℝ) / 32) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 22) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 324 22 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((371017 : ℝ) / 32)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell324Family23_2523 : safeFamily2523 324 23 ≤ ((3428221 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 23) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 324 23 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((3428221 : ℝ) / 256)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell324Family24_2523 : safeFamily2523 324 24 ≤ ((3039481 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 24) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 324 24 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((3039481 : ℝ) / 1024)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell324Family25_2523 : safeFamily2523 324 25 ≤ ((1905723 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 25) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 324 25 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((1905723 : ℝ) / 128)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell324Family26_2523 : safeFamily2523 324 26 ≤ ((39513 : ℝ) / 4) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 26) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 324 26 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((39513 : ℝ) / 4)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell324Family27_2523 : safeFamily2523 324 27 ≤ ((40959471 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 27) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 324 27 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((40959471 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell324Family28_2523 : safeFamily2523 324 28 ≤ ((17907611 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 28) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 324 28 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((17907611 : ℝ) / 512)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell324Family29_2523 : safeFamily2523 324 29 ≤ ((41827427 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 324 29) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 324 29 ≤ ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12539053258624271343445097298391543487748912944977331132891060764929181307) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 324 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((916319065303561342329084903949713293 : ℝ) / 10000000000000000000000000000000000000000000000000) ((41827427 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 324 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell324_2523 : (∑ i : Fin 30, safeFamily2523 324 i) ≤ ((680011255 : ℝ) / 1024) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell324Family0_2523 (add_le_add safeCell324Family1_2523 (add_le_add safeCell324Family2_2523 (add_le_add safeCell324Family3_2523 (add_le_add safeCell324Family4_2523 (add_le_add safeCell324Family5_2523 (add_le_add safeCell324Family6_2523 (add_le_add safeCell324Family7_2523 (add_le_add safeCell324Family8_2523 (add_le_add safeCell324Family9_2523 (add_le_add safeCell324Family10_2523 (add_le_add safeCell324Family11_2523 (add_le_add safeCell324Family12_2523 (add_le_add safeCell324Family13_2523 (add_le_add safeCell324Family14_2523 (add_le_add safeCell324Family15_2523 (add_le_add safeCell324Family16_2523 (add_le_add safeCell324Family17_2523 (add_le_add safeCell324Family18_2523 (add_le_add safeCell324Family19_2523 (add_le_add safeCell324Family20_2523 (add_le_add safeCell324Family21_2523 (add_le_add safeCell324Family22_2523 (add_le_add safeCell324Family23_2523 (add_le_add safeCell324Family24_2523 (add_le_add safeCell324Family25_2523 (add_le_add safeCell324Family26_2523 (add_le_add safeCell324Family27_2523 (add_le_add safeCell324Family28_2523 (safeCell324Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell325Family0_2523 : safeFamily2523 325 0 ≤ ((45460433 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 0) ^ 2) = ((10284403483257540047064865720519440496989684513819353738221977600097656250 : ℝ) / 342264947906071994799371423847409389739579209133301884832817364778899027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 325 0 ≤ ((4459190274783863324276915500064831803 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((10284403483257540047064865720519440496989684513819353738221977600097656250 : ℝ) / 342264947906071994799371423847409389739579209133301884832817364778899027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4459190274783863324276915500064831803 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((4459190274783863324276915500064831803 : ℝ) / 50000000000000000000000000000000000000000000000000) ((45460433 : ℝ) / 256)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell325Family1_2523 : safeFamily2523 325 1 ≤ ((7741047 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 1) ^ 2) = ((13174428200492576917246781152018019392239644040432558828662292480468750 : ℝ) / 438745872159761185252210665554804126108452614503180903177802571857161) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 325 1 ≤ ((9104074096489615314493622810651210619 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((13174428200492576917246781152018019392239644040432558828662292480468750 : ℝ) / 438745872159761185252210665554804126108452614503180903177802571857161) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9104074096489615314493622810651210619 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((9104074096489615314493622810651210619 : ℝ) / 100000000000000000000000000000000000000000000000000) ((7741047 : ℝ) / 256)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell325Family2_2523 : safeFamily2523 325 2 ≤ ((27571125 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 2) ^ 2) = ((344218181115607706483102558020079878576292604920044298988662292480468750 : ℝ) / 11467511618147061490940505968469918294417185174488339708513694909480201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 325 2 ≤ ((9201584955746206913274277580006705289 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((344218181115607706483102558020079878576292604920044298988662292480468750 : ℝ) / 11467511618147061490940505968469918294417185174488339708513694909480201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9201584955746206913274277580006705289 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((9201584955746206913274277580006705289 : ℝ) / 100000000000000000000000000000000000000000000000000) ((27571125 : ℝ) / 1024)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell325Family3_2523 : safeFamily2523 325 3 ≤ ((23433311 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 3) ^ 2) = ((45462269875261703511731947759291294284385179228648606456780433654785156250 : ℝ) / 1514860494306210776954940825139804515986095699627610308784765899935149027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 325 3 ≤ ((9256526637233142600001193963222969673 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((45462269875261703511731947759291294284385179228648606456780433654785156250 : ℝ) / 1514860494306210776954940825139804515986095699627610308784765899935149027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9256526637233142600001193963222969673 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((9256526637233142600001193963222969673 : ℝ) / 100000000000000000000000000000000000000000000000000) ((23433311 : ℝ) / 1024)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell325Family4_2523 : safeFamily2523 325 4 ≤ ((43961 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 4) ^ 2) = ((789842187514179514065072886606932778792047164099296824738164245605468750 : ℝ) / 26321645164766121743672850254698348301609003813796757233497093346980201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 325 4 ≤ ((1161164931730817056538068000682666909 : ℝ) / 12500000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((789842187514179514065072886606932778792047164099296824738164245605468750 : ℝ) / 26321645164766121743672850254698348301609003813796757233497093346980201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1161164931730817056538068000682666909 : ℝ) / 12500000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((1161164931730817056538068000682666909 : ℝ) / 12500000000000000000000000000000000000000000000000) ((43961 : ℝ) / 1024)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell325Family5_2523 : safeFamily2523 325 5 ≤ ((56435 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 5) ^ 2) = ((37502270134263936808481312283560250130002823235920536572773300964355468750 : ℝ) / 1248430166534593206641004775608959123853196617215321499768697699805447081) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 325 5 ≤ ((1124353260125476146910388357182741921 : ℝ) / 12500000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((37502270134263936808481312283560250130002823235920536572773300964355468750 : ℝ) / 1248430166534593206641004775608959123853196617215321499768697699805447081) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1124353260125476146910388357182741921 : ℝ) / 12500000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((1124353260125476146910388357182741921 : ℝ) / 12500000000000000000000000000000000000000000000000) ((56435 : ℝ) / 512)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell325Family6_2523 : safeFamily2523 325 6 ≤ ((13461 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 6) ^ 2) = ((65536000000000000000 : ℝ) / 2183101677524309333) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 325 6 ≤ ((458766154717738124088510898125967841 : ℝ) / 5000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((65536000000000000000 : ℝ) / 2183101677524309333) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((458766154717738124088510898125967841 : ℝ) / 5000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((458766154717738124088510898125967841 : ℝ) / 5000000000000000000000000000000000000000000000000) ((13461 : ℝ) / 256)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell325Family7_2523 : safeFamily2523 325 7 ≤ ((4323 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 7) ^ 2) = ((45462269875261703511731947759291294284385179228648606456780433654785156250 : ℝ) / 1514860494306210776954940825139804515986095699627610308784765899935149027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 325 7 ≤ ((9256526637233142600001193963222969673 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((45462269875261703511731947759291294284385179228648606456780433654785156250 : ℝ) / 1514860494306210776954940825139804515986095699627610308784765899935149027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9256526637233142600001193963222969673 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((9256526637233142600001193963222969673 : ℝ) / 100000000000000000000000000000000000000000000000000) ((4323 : ℝ) / 512)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell325Family8_2523 : safeFamily2523 325 8 ≤ ((567255 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 8) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 325 8 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((567255 : ℝ) / 512)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell325Family9_2523 : safeFamily2523 325 9 ≤ ((2107905 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 9) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 325 9 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((2107905 : ℝ) / 1024)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell325Family10_2523 : safeFamily2523 325 10 ≤ ((1854165 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 10) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 325 10 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1854165 : ℝ) / 1024)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell325Family11_2523 : safeFamily2523 325 11 ≤ ((441879 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 11) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 325 11 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((441879 : ℝ) / 256)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell325Family12_2523 : safeFamily2523 325 12 ≤ ((821877 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 12) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 325 12 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((821877 : ℝ) / 256)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell325Family13_2523 : safeFamily2523 325 13 ≤ ((779253 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 13) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 325 13 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((779253 : ℝ) / 512)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell325Family14_2523 : safeFamily2523 325 14 ≤ ((44707523 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 14) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 325 14 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((44707523 : ℝ) / 512)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell325Family15_2523 : safeFamily2523 325 15 ≤ ((105358317 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 15) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 325 15 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((105358317 : ℝ) / 1024)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell325Family16_2523 : safeFamily2523 325 16 ≤ ((257167 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 16) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 325 16 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((257167 : ℝ) / 128)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell325Family17_2523 : safeFamily2523 325 17 ≤ ((7891031 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 17) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 325 17 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((7891031 : ℝ) / 1024)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell325Family18_2523 : safeFamily2523 325 18 ≤ ((2944101 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 18) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 325 18 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((2944101 : ℝ) / 1024)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell325Family19_2523 : safeFamily2523 325 19 ≤ ((542601 : ℝ) / 64) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 19) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 325 19 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((542601 : ℝ) / 64)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell325Family20_2523 : safeFamily2523 325 20 ≤ ((4662731 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 20) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 325 20 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((4662731 : ℝ) / 512)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell325Family21_2523 : safeFamily2523 325 21 ≤ ((739357 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 21) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 325 21 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((739357 : ℝ) / 256)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell325Family22_2523 : safeFamily2523 325 22 ≤ ((11781899 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 22) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 325 22 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((11781899 : ℝ) / 1024)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell325Family23_2523 : safeFamily2523 325 23 ≤ ((13604541 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 23) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 325 23 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((13604541 : ℝ) / 1024)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell325Family24_2523 : safeFamily2523 325 24 ≤ ((3015129 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 24) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 325 24 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((3015129 : ℝ) / 1024)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell325Family25_2523 : safeFamily2523 325 25 ≤ ((945103 : ℝ) / 64) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 25) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 325 25 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((945103 : ℝ) / 64)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell325Family26_2523 : safeFamily2523 325 26 ≤ ((10031709 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 26) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 325 26 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((10031709 : ℝ) / 1024)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell325Family27_2523 : safeFamily2523 325 27 ≤ ((40614117 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 27) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 325 27 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((40614117 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell325Family28_2523 : safeFamily2523 325 28 ≤ ((35511053 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 28) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 325 28 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((35511053 : ℝ) / 1024)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell325Family29_2523 : safeFamily2523 325 29 ≤ ((41468483 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 325 29) ^ 2) = ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 325 29 ≤ ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((15057395139837368942107699481332033820372172807457787563141245178222656250 : ℝ) / 501364669792066291300799215874495833852328818921249678996792950716399027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 325 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((9055486237198780060132029044477417879 : ℝ) / 100000000000000000000000000000000000000000000000000) ((41468483 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 325 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell325_2523 : (∑ i : Fin 30, safeFamily2523 325 i) ≤ ((675518703 : ℝ) / 1024) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell325Family0_2523 (add_le_add safeCell325Family1_2523 (add_le_add safeCell325Family2_2523 (add_le_add safeCell325Family3_2523 (add_le_add safeCell325Family4_2523 (add_le_add safeCell325Family5_2523 (add_le_add safeCell325Family6_2523 (add_le_add safeCell325Family7_2523 (add_le_add safeCell325Family8_2523 (add_le_add safeCell325Family9_2523 (add_le_add safeCell325Family10_2523 (add_le_add safeCell325Family11_2523 (add_le_add safeCell325Family12_2523 (add_le_add safeCell325Family13_2523 (add_le_add safeCell325Family14_2523 (add_le_add safeCell325Family15_2523 (add_le_add safeCell325Family16_2523 (add_le_add safeCell325Family17_2523 (add_le_add safeCell325Family18_2523 (add_le_add safeCell325Family19_2523 (add_le_add safeCell325Family20_2523 (add_le_add safeCell325Family21_2523 (add_le_add safeCell325Family22_2523 (add_le_add safeCell325Family23_2523 (add_le_add safeCell325Family24_2523 (add_le_add safeCell325Family25_2523 (add_le_add safeCell325Family26_2523 (add_le_add safeCell325Family27_2523 (add_le_add safeCell325Family28_2523 (safeCell325Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell326Family0_2523 : safeFamily2523 326 0 ≤ ((89843033 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 0) ^ 2) = ((771330261244315503529864929038958037274226338536451530366648320007324218750 : ℝ) / 25651770542272481386560761482948829545185901621195314449900100036013673041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 326 0 ≤ ((873127737713345150818449014692778473 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((771330261244315503529864929038958037274226338536451530366648320007324218750 : ℝ) / 25651770542272481386560761482948829545185901621195314449900100036013673041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((873127737713345150818449014692778473 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((873127737713345150818449014692778473 : ℝ) / 10000000000000000000000000000000000000000000000000) ((89843033 : ℝ) / 512)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell326Family1_2523 : safeFamily2523 326 1 ≤ ((7688889 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 1) ^ 2) = ((36595633890257158103463280977827831645110122334534885635173034667968750 : ℝ) / 1218247524915273088824714541211074973638861997106211956728672445631769) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 326 1 ≤ ((8994556740751952072320680034382723987 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((36595633890257158103463280977827831645110122334534885635173034667968750 : ℝ) / 1218247524915273088824714541211074973638861997106211956728672445631769) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((8994556740751952072320680034382723987 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((8994556740751952072320680034382723987 : ℝ) / 100000000000000000000000000000000000000000000000000) ((7688889 : ℝ) / 256)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell326Family2_2523 : safeFamily2523 326 2 ≤ ((6864431 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 2) ^ 2) = ((956161614210021406897507105611332996045257235889011941635173034667968750 : ℝ) / 31846342797507931995931919658246789235671634571581183690072241796123929) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 326 2 ≤ ((9133700543710490000205539741283893199 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((956161614210021406897507105611332996045257235889011941635173034667968750 : ℝ) / 31846342797507931995931919658246789235671634571581183690072241796123929) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9133700543710490000205539741283893199 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((9133700543710490000205539741283893199 : ℝ) / 100000000000000000000000000000000000000000000000000) ((6864431 : ℝ) / 256)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell326Family3_2523 : safeFamily2523 326 3 ≤ ((23371151 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 3) ^ 2) = ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113596436522282890048228466579878464013674638408268446246296240172732423041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 326 3 ≤ ((9212368002644903129865086561176214139 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113596436522282890048228466579878464013674638408268446246296240172732423041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9212368002644903129865086561176214139 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((9212368002644903129865086561176214139 : ℝ) / 100000000000000000000000000000000000000000000000000) ((23371151 : ℝ) / 1024)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell326Family4_2523 : safeFamily2523 326 4 ≤ ((43883 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 4) ^ 2) = ((2194006076428276427958535796130368829977908789164713402050456237792968750 : ℝ) / 73107824871449766031299542675547983700093353014104565703915015233623929) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 326 4 ≤ ((9259413571164387889148712967972190501 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((2194006076428276427958535796130368829977908789164713402050456237792968750 : ℝ) / 73107824871449766031299542675547983700093353014104565703915015233623929) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9259413571164387889148712967972190501 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((9259413571164387889148712967972190501 : ℝ) / 100000000000000000000000000000000000000000000000000) ((43883 : ℝ) / 1024)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell326Family5_2523 : safeFamily2523 326 5 ≤ ((58345 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 5) ^ 2) = ((104172972595177602245781423009889583694452286766445934924370280456542968750 : ℝ) / 3465850401409101326959224898290789267894152929620078953517360019192491449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 326 5 ≤ ((1767878428400755432710283771517108381 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((104172972595177602245781423009889583694452286766445934924370280456542968750 : ℝ) / 3465850401409101326959224898290789267894152929620078953517360019192491449) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1767878428400755432710283771517108381 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((1767878428400755432710283771517108381 : ℝ) / 20000000000000000000000000000000000000000000000000) ((58345 : ℝ) / 512)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell326Family6_2523 : safeFamily2523 326 6 ≤ ((55225 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 6) ^ 2) = ((1228800000000000000000 : ℝ) / 40921345293156351991) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 326 6 ≤ ((9096165996529030812026349366489839997 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1228800000000000000000 : ℝ) / 40921345293156351991) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9096165996529030812026349366489839997 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((9096165996529030812026349366489839997 : ℝ) / 100000000000000000000000000000000000000000000000000) ((55225 : ℝ) / 1024)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell326Family7_2523 : safeFamily2523 326 7 ≤ ((8827 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 7) ^ 2) = ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113596436522282890048228466579878464013674638408268446246296240172732423041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 326 7 ≤ ((9212368002644903129865086561176214139 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 113596436522282890048228466579878464013674638408268446246296240172732423041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9212368002644903129865086561176214139 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((9212368002644903129865086561176214139 : ℝ) / 100000000000000000000000000000000000000000000000000) ((8827 : ℝ) / 1024)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell326Family8_2523 : safeFamily2523 326 8 ≤ ((568353 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 8) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 326 8 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((568353 : ℝ) / 512)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell326Family9_2523 : safeFamily2523 326 9 ≤ ((2101629 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 9) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 326 9 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((2101629 : ℝ) / 1024)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell326Family10_2523 : safeFamily2523 326 10 ≤ ((922743 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 10) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 326 10 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((922743 : ℝ) / 512)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell326Family11_2523 : safeFamily2523 326 11 ≤ ((219711 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 11) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 326 11 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((219711 : ℝ) / 128)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell326Family12_2523 : safeFamily2523 326 12 ≤ ((3266735 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 12) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 326 12 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((3266735 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell326Family13_2523 : safeFamily2523 326 13 ≤ ((48367 : ℝ) / 32) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 13) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 326 13 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((48367 : ℝ) / 32)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell326Family14_2523 : safeFamily2523 326 14 ≤ ((22179565 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 14) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 326 14 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((22179565 : ℝ) / 256)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell326Family15_2523 : safeFamily2523 326 15 ≤ ((104482849 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 15) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 326 15 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((104482849 : ℝ) / 1024)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell326Family16_2523 : safeFamily2523 326 16 ≤ ((2039571 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 16) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 326 16 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((2039571 : ℝ) / 1024)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell326Family17_2523 : safeFamily2523 326 17 ≤ ((3909307 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 17) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 326 17 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((3909307 : ℝ) / 512)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell326Family18_2523 : safeFamily2523 326 18 ≤ ((1458277 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 18) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 326 18 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1458277 : ℝ) / 512)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell326Family19_2523 : safeFamily2523 326 19 ≤ ((8597831 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 19) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 326 19 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((8597831 : ℝ) / 1024)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell326Family20_2523 : safeFamily2523 326 20 ≤ ((9232823 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 20) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 326 20 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((9232823 : ℝ) / 1024)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell326Family21_2523 : safeFamily2523 326 21 ≤ ((2927423 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 21) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 326 21 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((2927423 : ℝ) / 1024)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell326Family22_2523 : safeFamily2523 326 22 ≤ ((11661179 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 22) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 326 22 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((11661179 : ℝ) / 1024)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell326Family23_2523 : safeFamily2523 326 23 ≤ ((3365385 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 23) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 326 23 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((3365385 : ℝ) / 256)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell326Family24_2523 : safeFamily2523 326 24 ≤ ((1491551 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 24) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 326 24 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1491551 : ℝ) / 512)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell326Family25_2523 : safeFamily2523 326 25 ≤ ((14959059 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 25) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 326 25 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((14959059 : ℝ) / 1024)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell326Family26_2523 : safeFamily2523 326 26 ≤ ((9922603 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 26) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 326 26 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((9922603 : ℝ) / 1024)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell326Family27_2523 : safeFamily2523 326 27 ≤ ((40165711 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 27) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 326 27 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((40165711 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell326Family28_2523 : safeFamily2523 326 28 ≤ ((35116825 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 28) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 326 28 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((35116825 : ℝ) / 1024)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell326Family29_2523 : safeFamily2523 326 29 ≤ ((41004443 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 326 29) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 326 29 ≤ ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 37584249683722053624167845884980312853642122355291399012198268981326173041) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 326 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((4462726134964930303862938766765104447 : ℝ) / 50000000000000000000000000000000000000000000000000) ((41004443 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 326 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell326_2523 : (∑ i : Fin 30, safeFamily2523 326 i) ≤ ((669159497 : ℝ) / 1024) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell326Family0_2523 (add_le_add safeCell326Family1_2523 (add_le_add safeCell326Family2_2523 (add_le_add safeCell326Family3_2523 (add_le_add safeCell326Family4_2523 (add_le_add safeCell326Family5_2523 (add_le_add safeCell326Family6_2523 (add_le_add safeCell326Family7_2523 (add_le_add safeCell326Family8_2523 (add_le_add safeCell326Family9_2523 (add_le_add safeCell326Family10_2523 (add_le_add safeCell326Family11_2523 (add_le_add safeCell326Family12_2523 (add_le_add safeCell326Family13_2523 (add_le_add safeCell326Family14_2523 (add_le_add safeCell326Family15_2523 (add_le_add safeCell326Family16_2523 (add_le_add safeCell326Family17_2523 (add_le_add safeCell326Family18_2523 (add_le_add safeCell326Family19_2523 (add_le_add safeCell326Family20_2523 (add_le_add safeCell326Family21_2523 (add_le_add safeCell326Family22_2523 (add_le_add safeCell326Family23_2523 (add_le_add safeCell326Family24_2523 (add_le_add safeCell326Family25_2523 (add_le_add safeCell326Family26_2523 (add_le_add safeCell326Family27_2523 (add_le_add safeCell326Family28_2523 (safeCell326Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h

theorem safeCell327Family0_2523 : safeFamily2523 327 0 ≤ ((5527121 : ℝ) / 32) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 0) ^ 2) = ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8543459660791495707517307192107507699647633636476309366230468794087927323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 327 0 ≤ ((2128720244312214124801155224648529813 : ℝ) / 25000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((257110087081438501176621643012986012424742112845483843455549440002441406250 : ℝ) / 8543459660791495707517307192107507699647633636476309366230468794087927323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2128720244312214124801155224648529813 : ℝ) / 25000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((2128720244312214124801155224648529813 : ℝ) / 25000000000000000000000000000000000000000000000000) ((5527121 : ℝ) / 32)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell327Family1_2523 : safeFamily2523 327 1 ≤ ((7620227 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 1) ^ 2) = ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10959005175434236543560897690570986665522462878309817192782492036625889) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 327 1 ≤ ((177334256734524472191852393003081973 : ℝ) / 2000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((329360705012314422931169528800450484805991101010813970716557312011718750 : ℝ) / 10959005175434236543560897690570986665522462878309817192782492036625889) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((177334256734524472191852393003081973 : ℝ) / 2000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((177334256734524472191852393003081973 : ℝ) / 2000000000000000000000000000000000000000000000000) ((7620227 : ℝ) / 256)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell327Family2_2523 : safeFamily2523 327 2 ≤ ((27307907 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 2) ^ 2) = ((175621520977350870654644162255142795191986022918389948463603210449218750 : ℝ) / 5847622946871833629991892776305348848273632441099861357678392175105201) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 327 2 ≤ ((1810815248557320098257873855279144387 : ℝ) / 20000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((175621520977350870654644162255142795191986022918389948463603210449218750 : ℝ) / 5847622946871833629991892776305348848273632441099861357678392175105201) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1810815248557320098257873855279144387 : ℝ) / 20000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((1810815248557320098257873855279144387 : ℝ) / 20000000000000000000000000000000000000000000000000) ((27307907 : ℝ) / 1024)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell327Family3_2523 : safeFamily2523 327 3 ≤ ((11644433 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 3) ^ 2) = ((23195035650643726281495891713924129736931213892167656355500221252441406250 : ℝ) / 772619353485611535947072290294232364404296855078245305408758819857024027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 327 3 ≤ ((9160434041079995132552156859076217811 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((23195035650643726281495891713924129736931213892167656355500221252441406250 : ℝ) / 772619353485611535947072290294232364404296855078245305408758819857024027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9160434041079995132552156859076217811 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((9160434041079995132552156859076217811 : ℝ) / 100000000000000000000000000000000000000000000000000) ((11644433 : ℝ) / 512)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell327Family4_2523 : safeFamily2523 327 4 ≤ ((43779 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 4) ^ 2) = ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 657886863062196354187911353194672843745203455596603644650826177517654849) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 327 4 ≤ ((4612093057985171967534924129851506049 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((19746054687854487851626822165173319469801179102482420618454106140136718750 : ℝ) / 657886863062196354187911353194672843745203455596603644650826177517654849) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((4612093057985171967534924129851506049 : ℝ) / 50000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((4612093057985171967534924129851506049 : ℝ) / 50000000000000000000000000000000000000000000000000) ((43779 : ℝ) / 1024)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell327Family5_2523 : safeFamily2523 327 5 ≤ ((7537 : ℝ) / 64) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 5) ^ 2) = ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31171262052783917678624184177990796964804375654814324230447546518982531969) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 327 5 ≤ ((865893073254867449764586233047590593 : ℝ) / 10000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((937556753356598420212032807089006253250070580898013414319332524108886718750 : ℝ) / 31171262052783917678624184177990796964804375654814324230447546518982531969) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((865893073254867449764586233047590593 : ℝ) / 10000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((865893073254867449764586233047590593 : ℝ) / 10000000000000000000000000000000000000000000000000) ((7537 : ℝ) / 64)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell327Family6_2523 : safeFamily2523 327 6 ≤ ((28321 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 6) ^ 2) = ((1638400000000000000000 : ℝ) / 54543182198691157317) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 327 6 ≤ ((9003438594611161277886115737641306937 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1638400000000000000000 : ℝ) / 54543182198691157317) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9003438594611161277886115737641306937 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((9003438594611161277886115737641306937 : ℝ) / 100000000000000000000000000000000000000000000000000) ((28321 : ℝ) / 512)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell327Family7_2523 : safeFamily2523 327 7 ≤ ((2253 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 7) ^ 2) = ((23195035650643726281495891713924129736931213892167656355500221252441406250 : ℝ) / 772619353485611535947072290294232364404296855078245305408758819857024027) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 327 7 ≤ ((9160434041079995132552156859076217811 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((23195035650643726281495891713924129736931213892167656355500221252441406250 : ℝ) / 772619353485611535947072290294232364404296855078245305408758819857024027) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((9160434041079995132552156859076217811 : ℝ) / 100000000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((9160434041079995132552156859076217811 : ℝ) / 100000000000000000000000000000000000000000000000000) ((2253 : ℝ) / 256)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell327Family8_2523 : safeFamily2523 327 8 ≤ ((283957 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 8) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 327 8 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((283957 : ℝ) / 256)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell327Family9_2523 : safeFamily2523 327 9 ≤ ((2089795 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 9) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 327 9 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((2089795 : ℝ) / 1024)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell327Family10_2523 : safeFamily2523 327 10 ≤ ((1831977 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 10) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 327 10 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((1831977 : ℝ) / 1024)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell327Family11_2523 : safeFamily2523 327 11 ≤ ((1743287 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 11) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 327 11 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((1743287 : ℝ) / 1024)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell327Family12_2523 : safeFamily2523 327 12 ≤ ((3237509 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 12) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 327 12 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((3237509 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell327Family13_2523 : safeFamily2523 327 13 ≤ ((383249 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 13) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 327 13 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((383249 : ℝ) / 256)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell327Family14_2523 : safeFamily2523 327 14 ≤ ((87794527 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 14) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 327 14 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((87794527 : ℝ) / 1024)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell327Family15_2523 : safeFamily2523 327 15 ≤ ((103341243 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 15) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 327 15 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((103341243 : ℝ) / 1024)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell327Family16_2523 : safeFamily2523 327 16 ≤ ((2016625 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 16) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 327 16 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((2016625 : ℝ) / 1024)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell327Family17_2523 : safeFamily2523 327 17 ≤ ((1931607 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 17) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 327 17 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((1931607 : ℝ) / 256)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell327Family18_2523 : safeFamily2523 327 18 ≤ ((1440823 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 18) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 327 18 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((1440823 : ℝ) / 512)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell327Family19_2523 : safeFamily2523 327 19 ≤ ((8492401 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 19) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 327 19 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((8492401 : ℝ) / 1024)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell327Family20_2523 : safeFamily2523 327 20 ≤ ((1139625 : ℝ) / 128) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 20) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 327 20 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((1139625 : ℝ) / 128)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell327Family21_2523 : safeFamily2523 327 21 ≤ ((1445041 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 21) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 327 21 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((1445041 : ℝ) / 512)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell327Family22_2523 : safeFamily2523 327 22 ≤ ((11511263 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 22) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 327 22 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((11511263 : ℝ) / 1024)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell327Family23_2523 : safeFamily2523 327 23 ≤ ((13284919 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 23) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 327 23 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((13284919 : ℝ) / 1024)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell327Family24_2523 : safeFamily2523 327 24 ≤ ((2943633 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 24) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 327 24 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((2943633 : ℝ) / 1024)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell327Family25_2523 : safeFamily2523 327 25 ≤ ((3689799 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 25) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 327 25 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((3689799 : ℝ) / 256)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell327Family26_2523 : safeFamily2523 327 26 ≤ ((2447201 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 26) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 327 26 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((2447201 : ℝ) / 256)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell327Family27_2523 : safeFamily2523 327 27 ≤ ((39617507 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 27) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 327 27 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((39617507 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell327Family28_2523 : safeFamily2523 327 28 ≤ ((17317697 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 28) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 327 28 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((17317697 : ℝ) / 512)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell327Family29_2523 : safeFamily2523 327 29 ≤ ((40438671 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 327 29) ^ 2) = ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 327 29 ≤ ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((376434878495934223552692487033300845509304320186444689078531129455566406250 : ℝ) / 12520952707941353120053001992784668802466373881175004220329858442525427323) ((9357622968840234435347668149807114730006835588534480734341264379457 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) 30
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower30_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 327 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((548376458643307283787086052397637561 : ℝ) / 6250000000000000000000000000000000000000000000000) ((40438671 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 327 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell327_2523 : (∑ i : Fin 30, safeFamily2523 327 i) ≤ ((660986309 : ℝ) / 1024) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell327Family0_2523 (add_le_add safeCell327Family1_2523 (add_le_add safeCell327Family2_2523 (add_le_add safeCell327Family3_2523 (add_le_add safeCell327Family4_2523 (add_le_add safeCell327Family5_2523 (add_le_add safeCell327Family6_2523 (add_le_add safeCell327Family7_2523 (add_le_add safeCell327Family8_2523 (add_le_add safeCell327Family9_2523 (add_le_add safeCell327Family10_2523 (add_le_add safeCell327Family11_2523 (add_le_add safeCell327Family12_2523 (add_le_add safeCell327Family13_2523 (add_le_add safeCell327Family14_2523 (add_le_add safeCell327Family15_2523 (add_le_add safeCell327Family16_2523 (add_le_add safeCell327Family17_2523 (add_le_add safeCell327Family18_2523 (add_le_add safeCell327Family19_2523 (add_le_add safeCell327Family20_2523 (add_le_add safeCell327Family21_2523 (add_le_add safeCell327Family22_2523 (add_le_add safeCell327Family23_2523 (add_le_add safeCell327Family24_2523 (add_le_add safeCell327Family25_2523 (add_le_add safeCell327Family26_2523 (add_le_add safeCell327Family27_2523 (add_le_add safeCell327Family28_2523 (safeCell327Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h


end ConnesWeilRH.Dev
