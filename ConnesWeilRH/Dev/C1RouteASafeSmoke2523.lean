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

theorem safeCell443Family0_2523 : safeFamily2523 443 0 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 0) ^ 2) = ((771330261244315503529864929038958037274226338536451530366648320007324218750 : ℝ) / 816169500701140872297629889807045457062075260420760696606768032390138449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]
  have hu : ownerProductionExpUpper2514 443 0 ≤ ((1 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((771330261244315503529864929038958037274226338536451530366648320007324218750 : ℝ) / 816169500701140872297629889807045457062075260420760696606768032390138449) ((1 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) ((1 : ℝ) / 100000000000000000000000000000000000000000000000000) 945
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower945_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 0 ((359663972556928197349 : ℝ) / 100000000000000000000) ((1 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight0_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 0 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad0_2460, mod0_2460, coef0_2460]

theorem safeCell443Family1_2523 : safeFamily2523 443 1 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 1) ^ 2) = ((36595633890257158103463280977827831645110122334534885635173034667968750 : ℝ) / 544538729299731082686934278810310431317794658760548063681435791887641) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]
  have hu : ownerProductionExpUpper2514 443 1 ≤ ((32529864444494081901 : ℝ) / 5000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((36595633890257158103463280977827831645110122334534885635173034667968750 : ℝ) / 544538729299731082686934278810310431317794658760548063681435791887641) ((399245212284354641404123006881170829632496910361813 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((32529864444494081901 : ℝ) / 5000000000000000000000000000000000000000000000000) 67
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower67_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 1 ((135866912882797428059 : ℝ) / 25000000000000000000) ((32529864444494081901 : ℝ) / 5000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight1_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 1 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad1_2460, mod1_2460, coef1_2460]

theorem safeCell443Family2_2523 : safeFamily2523 443 2 ≤ ((13 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 2) ^ 2) = ((956161614210021406897507105611332996045257235889011941635173034667968750 : ℝ) / 21067002067659259897727435459834556558534557158050561401316455336217881) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]
  have hu : ownerProductionExpUpper2514 443 2 ≤ ((1944502309627075507867638029421 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((956161614210021406897507105611332996045257235889011941635173034667968750 : ℝ) / 21067002067659259897727435459834556558534557158050561401316455336217881) ((22363426410542352327125191277648092412819973109887261303759 : ℝ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000) ((1944502309627075507867638029421 : ℝ) / 100000000000000000000000000000000000000000000000000) 45
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower45_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 2 ((434946487129461636391 : ℝ) / 50000000000000000000) ((1944502309627075507867638029421 : ℝ) / 100000000000000000000000000000000000000000000000000) ((13 : ℝ) / 1024)
    safeWeight2_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 2 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad2_2460, mod2_2460, coef2_2460]

theorem safeCell443Family3_2523 : safeFamily2523 443 3 ≤ ((7719 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 3) ^ 2) = ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 88760835480711549533965334986736679925550812047493892493002908169108888449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]
  have hu : ownerProductionExpUpper2514 443 3 ≤ ((2074700790945167443664382213793029 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 88760835480711549533965334986736679925550812047493892493002908169108888449) ((1569566396024027525907947400051077034316726897844114189260505281 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2074700790945167443664382213793029 : ℝ) / 100000000000000000000000000000000000000000000000000) 38
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower38_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 3 ((737468227129887756671 : ℝ) / 50000000000000000000) ((2074700790945167443664382213793029 : ℝ) / 100000000000000000000000000000000000000000000000000) ((7719 : ℝ) / 1024)
    safeWeight3_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 3 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad3_2460, mod3_2460, coef3_2460]

theorem safeCell443Family4_2523 : safeFamily2523 443 4 ≤ ((153 : ℝ) / 512) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 4) ^ 2) = ((2194006076428276427958535796130368829977908789164713402050456237792968750 : ℝ) / 62328484141601093933095058477135751022956275600573943415159228773717881) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]
  have hu : ownerProductionExpUpper2514 443 4 ≤ ((6448246107659408117666153154263629 : ℝ) / 12500000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((2194006076428276427958535796130368829977908789164713402050456237792968750 : ℝ) / 62328484141601093933095058477135751022956275600573943415159228773717881) ((31525583800735182089857647634399997075973016458995038091757465551 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((6448246107659408117666153154263629 : ℝ) / 12500000000000000000000000000000000000000000000000) 35
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower35_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 4 ((1324543307508375172527 : ℝ) / 50000000000000000000) ((6448246107659408117666153154263629 : ℝ) / 12500000000000000000000000000000000000000000000000) ((153 : ℝ) / 512)
    safeWeight4_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 4 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad4_2460, mod4_2460, coef4_2460]

theorem safeCell443Family5_2523 : safeFamily2523 443 5 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 5) ^ 2) = ((104172972595177602245781423009889583694452286766445934924370280456542968750 : ℝ) / 706339174567841269818876943497257702547061111756239647595878685456543161) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]
  have hu : ownerProductionExpUpper2514 443 5 ≤ ((1 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((104172972595177602245781423009889583694452286766445934924370280456542968750 : ℝ) / 706339174567841269818876943497257702547061111756239647595878685456543161) ((112590355544073 : ℝ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000) ((1 : ℝ) / 100000000000000000000000000000000000000000000000000) 147
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower147_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 5 ((20504367504119714551 : ℝ) / 5000000000000000000) ((1 : ℝ) / 100000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight5_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 5 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad5_2460, mod5_2460, coef5_2460]

theorem safeCell443Family6_2523 : safeFamily2523 443 6 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 6) ^ 2) = ((4915200000000000000000 : ℝ) / 98861437795827696871) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]
  have hu : ownerProductionExpUpper2514 443 6 ≤ ((12784567651973979301633760197 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((4915200000000000000000 : ℝ) / 98861437795827696871) ((26214428316817593447005476274726330850754122814407262856101 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((12784567651973979301633760197 : ℝ) / 50000000000000000000000000000000000000000000000000) 49
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower49_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 6 ((184726402473266255681 : ℝ) / 25000000000000000000) ((12784567651973979301633760197 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight6_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 6 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad6_2460, mod6_2460, coef6_2460]

theorem safeCell443Family7_2523 : safeFamily2523 443 7 ≤ ((17 : ℝ) / 256) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 7) ^ 2) = ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 88760835480711549533965334986736679925550812047493892493002908169108888449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]
  have hu : ownerProductionExpUpper2514 443 7 ≤ ((2074700790945167443664382213793029 : ℝ) / 100000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((3409670240644627763379896081946847071328888442148645484258532524108886718750 : ℝ) / 88760835480711549533965334986736679925550812047493892493002908169108888449) ((1569566396024027525907947400051077034316726897844114189260505281 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((2074700790945167443664382213793029 : ℝ) / 100000000000000000000000000000000000000000000000000) 38
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower38_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 7 ((737468227129887756671 : ℝ) / 50000000000000000000) ((2074700790945167443664382213793029 : ℝ) / 100000000000000000000000000000000000000000000000000) ((17 : ℝ) / 256)
    safeWeight7_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 7 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad7_2460, mod7_2460, coef7_2460]

theorem safeCell443Family8_2523 : safeFamily2523 443 8 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 8) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]
  have hu : ownerProductionExpUpper2514 443 8 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 8 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight8_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 8 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad8_2460, mod8_2460, coef8_2460]

theorem safeCell443Family9_2523 : safeFamily2523 443 9 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 9) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]
  have hu : ownerProductionExpUpper2514 443 9 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 9 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight9_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 9 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad9_2460, mod9_2460, coef9_2460]

theorem safeCell443Family10_2523 : safeFamily2523 443 10 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 10) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]
  have hu : ownerProductionExpUpper2514 443 10 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 10 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight10_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 10 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad10_2460, mod10_2460, coef10_2460]

theorem safeCell443Family11_2523 : safeFamily2523 443 11 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 11) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]
  have hu : ownerProductionExpUpper2514 443 11 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 11 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight11_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 11 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad11_2460, mod11_2460, coef11_2460]

theorem safeCell443Family12_2523 : safeFamily2523 443 12 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 12) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]
  have hu : ownerProductionExpUpper2514 443 12 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 12 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight12_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 12 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad12_2460, mod12_2460, coef12_2460]

theorem safeCell443Family13_2523 : safeFamily2523 443 13 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 13) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]
  have hu : ownerProductionExpUpper2514 443 13 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 13 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight13_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 13 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad13_2460, mod13_2460, coef13_2460]

theorem safeCell443Family14_2523 : safeFamily2523 443 14 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 14) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]
  have hu : ownerProductionExpUpper2514 443 14 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 14 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight14_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 14 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad14_2460, mod14_2460, coef14_2460]

theorem safeCell443Family15_2523 : safeFamily2523 443 15 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 15) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]
  have hu : ownerProductionExpUpper2514 443 15 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 15 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight15_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 15 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad15_2460, mod15_2460, coef15_2460]

theorem safeCell443Family16_2523 : safeFamily2523 443 16 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 16) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]
  have hu : ownerProductionExpUpper2514 443 16 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 16 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight16_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 16 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad16_2460, mod16_2460, coef16_2460]

theorem safeCell443Family17_2523 : safeFamily2523 443 17 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 17) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]
  have hu : ownerProductionExpUpper2514 443 17 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 17 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight17_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 17 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad17_2460, mod17_2460, coef17_2460]

theorem safeCell443Family18_2523 : safeFamily2523 443 18 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 18) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]
  have hu : ownerProductionExpUpper2514 443 18 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 18 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight18_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 18 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad18_2460, mod18_2460, coef18_2460]

theorem safeCell443Family19_2523 : safeFamily2523 443 19 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 19) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]
  have hu : ownerProductionExpUpper2514 443 19 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 19 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight19_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 19 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad19_2460, mod19_2460, coef19_2460]

theorem safeCell443Family20_2523 : safeFamily2523 443 20 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 20) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]
  have hu : ownerProductionExpUpper2514 443 20 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 20 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight20_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 20 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad20_2460, mod20_2460, coef20_2460]

theorem safeCell443Family21_2523 : safeFamily2523 443 21 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 21) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]
  have hu : ownerProductionExpUpper2514 443 21 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 21 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight21_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 21 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad21_2460, mod21_2460, coef21_2460]

theorem safeCell443Family22_2523 : safeFamily2523 443 22 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 22) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]
  have hu : ownerProductionExpUpper2514 443 22 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 22 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight22_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 22 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad22_2460, mod22_2460, coef22_2460]

theorem safeCell443Family23_2523 : safeFamily2523 443 23 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 23) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]
  have hu : ownerProductionExpUpper2514 443 23 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 23 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight23_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 23 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad23_2460, mod23_2460, coef23_2460]

theorem safeCell443Family24_2523 : safeFamily2523 443 24 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 24) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]
  have hu : ownerProductionExpUpper2514 443 24 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 24 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight24_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 24 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad24_2460, mod24_2460, coef24_2460]

theorem safeCell443Family25_2523 : safeFamily2523 443 25 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 25) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]
  have hu : ownerProductionExpUpper2514 443 25 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 25 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight25_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 25 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad25_2460, mod25_2460, coef25_2460]

theorem safeCell443Family26_2523 : safeFamily2523 443 26 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 26) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]
  have hu : ownerProductionExpUpper2514 443 26 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 26 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight26_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 26 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad26_2460, mod26_2460, coef26_2460]

theorem safeCell443Family27_2523 : safeFamily2523 443 27 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 27) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]
  have hu : ownerProductionExpUpper2514 443 27 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 27 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight27_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 27 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad27_2460, mod27_2460, coef27_2460]

theorem safeCell443Family28_2523 : safeFamily2523 443 28 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 28) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]
  have hu : ownerProductionExpUpper2514 443 28 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 28 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight28_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 28 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad28_2460, mod28_2460, coef28_2460]

theorem safeCell443Family29_2523 : safeFamily2523 443 29 ≤ ((1 : ℝ) / 1024) := by
  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) 443 29) ^ 2) = ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) := by
    norm_num [ownerCellLowerRatio2501, stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]
  have hu : ownerProductionExpUpper2514 443 29 ≤ ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) := by
    unfold ownerProductionExpUpper2514
    rw [hz]
    apply split_upper_rational2523 ((1129304635487802670658077461099902536527912960559334067235593388366699218750 : ℝ) / 12748648642150713109904714291838528765518295994516845258904936977702638449) ((302730094770064971941855018556802521144809 : ℝ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) 88
    · apply (Nat.floor_eq_iff' (by norm_num)).mpr
      constructor <;> norm_num
    · exact safePower88_2523
    · norm_num
    · norm_num
    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]
  apply safeFamily_le_rational2523 443 29 ((470581980927366937457 : ℝ) / 100000000000000000000) ((169108464121 : ℝ) / 50000000000000000000000000000000000000000000000000) ((1 : ℝ) / 1024)
    safeWeight29_2523 hu (by norm_num)
    (safeFactor_owner_nonneg2523 443 29 (by omega) (by omega))
  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,
    stripRadius2303, ownerRad_2463, ownerMod_2463, ownerCoef_2463, rad29_2460, mod29_2460, coef29_2460]

theorem safeCell443_2523 : (∑ i : Fin 30, safeFamily2523 443 i) ≤ ((2033 : ℝ) / 256) := by
  rw [safe_sum30_chain2523]
  have h := add_le_add safeCell443Family0_2523 (add_le_add safeCell443Family1_2523 (add_le_add safeCell443Family2_2523 (add_le_add safeCell443Family3_2523 (add_le_add safeCell443Family4_2523 (add_le_add safeCell443Family5_2523 (add_le_add safeCell443Family6_2523 (add_le_add safeCell443Family7_2523 (add_le_add safeCell443Family8_2523 (add_le_add safeCell443Family9_2523 (add_le_add safeCell443Family10_2523 (add_le_add safeCell443Family11_2523 (add_le_add safeCell443Family12_2523 (add_le_add safeCell443Family13_2523 (add_le_add safeCell443Family14_2523 (add_le_add safeCell443Family15_2523 (add_le_add safeCell443Family16_2523 (add_le_add safeCell443Family17_2523 (add_le_add safeCell443Family18_2523 (add_le_add safeCell443Family19_2523 (add_le_add safeCell443Family20_2523 (add_le_add safeCell443Family21_2523 (add_le_add safeCell443Family22_2523 (add_le_add safeCell443Family23_2523 (add_le_add safeCell443Family24_2523 (add_le_add safeCell443Family25_2523 (add_le_add safeCell443Family26_2523 (add_le_add safeCell443Family27_2523 (add_le_add safeCell443Family28_2523 (safeCell443Family29_2523)))))))))))))))))))))))))))))
  norm_num at h ⊢
  exact h


end ConnesWeilRH.Dev
