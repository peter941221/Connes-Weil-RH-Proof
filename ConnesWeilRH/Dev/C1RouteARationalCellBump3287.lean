import ConnesWeilRH.Dev.C1RouteARationalBump3286

namespace ConnesWeilRH.Dev

def storedWidthRat3287 : Fin 30 → ℚ :=
  ![((3602879701896397 : ℚ) / 2251799813685248),
    ((517913957147607 : ℚ) / 281474976710656),
    ((1170935903116329 : ℚ) / 562949953421312),
    ((5224175567749775 : ℚ) / 2251799813685248),
    ((1441151880758559 : ℚ) / 562949953421312),
    ((3783023686991217 : ℚ) / 2251799813685248),
    (2 : ℚ),
    ((5224175567749775 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248),
    ((3963167672086037 : ℚ) / 2251799813685248)]

theorem storedWidthRat_cast3287 (family : Fin 30) :
    (storedWidthRat3287 family : ℝ) =
      C1RouteAOwnerScaleAudit.storedWidth family := by
  fin_cases family <;>
    norm_num [storedWidthRat3287,
      C1RouteAOwnerScaleAudit.storedWidth, Matrix.cons_val_zero,
      Matrix.cons_val_four, Fin.ext_iff]

def ratCellBumpInterval3287 (index : ℕ) (family : Fin 30) : RatInterval3276 :=
  let radius := storedWidthRat3287 family ^ 2
  let position := |record2680CenterRat3279 index|
  let t := ratBumpT3286 radius position
  if |record2680CenterRat3279 index| < radius then
    ratBumpInterval3286 t
  else
    { lo := 0, hi := 0 }


theorem ratBumpT_nonpos3287
    {radius position : ℝ}
    (hradius : 0 < radius) (hposition : 0 ≤ position)
    (hinside : position < radius) :
    30 - 30 / (1 - (position / radius) ^ 2) ≤ 0 := by
  have hratio0 : 0 ≤ position / radius := div_nonneg hposition hradius.le
  have hratio1 : position / radius < 1 := (div_lt_one hradius).mpr hinside
  have hqpos : 0 < 1 - (position / radius) ^ 2 := by
    nlinarith [sq_nonneg (position / radius)]
  have hqle : 1 - (position / radius) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (position / radius)]
  have hinv : 1 ≤ 1 / (1 - (position / radius) ^ 2) := by
    exact (one_le_div hqpos).2 hqle
  have hmul := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 30)
  have hmul' : 30 ≤ 30 / (1 - (position / radius) ^ 2) := by
    calc
      30 = 30 * 1 := by ring
      _ ≤ 30 * (1 / (1 - (position / radius) ^ 2)) := by exact hmul
      _ = 30 / (1 - (position / radius) ^ 2) := by ring
  linarith

theorem ratCellBumpInterval_mem3287
    {index : ℕ} (family : Fin 30) (hindex : index < 40960) :
    (ratCellBumpInterval3287 index family).Mem
      (C1RouteAOwnerScaleAudit.widthBump
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index)) := by
  let radiusQ := storedWidthRat3287 family ^ 2
  let positionQ := |record2680CenterRat3279 index|
  let tQ := ratBumpT3286 radiusQ positionQ
  have hradiusQ : 0 < radiusQ := by
    dsimp [radiusQ]
    fin_cases family <;>
      norm_num [storedWidthRat3287, Matrix.cons_val_zero,
        Matrix.cons_val_four, Fin.ext_iff]
  have hradius : 0 < (radiusQ : ℝ) := by exact_mod_cast hradiusQ
  have hcenter : (record2680CenterRat3279 index : ℝ) =
      record2680Center3212 index := record2680CenterRat_cast3279 index
  have hposition : (positionQ : ℝ) =
      |record2680Center3212 index| := by
    dsimp [positionQ]
    rw [Rat.cast_abs, hcenter]
  have hradiusCast : (radiusQ : ℝ) =
      C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
    dsimp [radiusQ]
    rw [Rat.cast_pow, storedWidthRat_cast3287]
  by_cases hactive : |record2680CenterRat3279 index| < radiusQ
  · have hactiveR : |record2680Center3212 index| < (radiusQ : ℝ) := by
      have hp : (positionQ : ℝ) < (radiusQ : ℝ) := by
        exact_mod_cast hactive
      rw [hposition] at hp
      exact hp
    have hpos : 0 ≤ (positionQ : ℝ) := by
      dsimp [positionQ]
      positivity
    have hinside : (positionQ : ℝ) < (radiusQ : ℝ) := by
      rw [hposition]
      exact hactiveR
    have ht : (tQ : ℝ) = 30 - 30 /
        (1 - ((positionQ : ℝ) / (radiusQ : ℝ)) ^ 2) := by
      dsimp [tQ, ratBumpT3286]
      norm_num [Rat.cast_sub, Rat.cast_div, Rat.cast_pow]
    have ht0' := ratBumpT_nonpos3287 hradius hpos hinside
    have ht0 : (tQ : ℝ) ≤ 0 := by
      simpa [tQ, ratBumpT3286] using ht0'
    have hmem := ratBumpInterval_mem3286
      (radius := radiusQ) (position := positionQ) (t := tQ)
      hradius hpos hinside ht ht0
    have heven : C1RouteAOwnerScaleAudit.widthBump
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index) =
        C1RouteAOwnerScaleAudit.widthBump (radiusQ : ℝ) (positionQ : ℝ) := by
      have hleft : |record2680Center3212 index| <
          C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
        simpa [hradiusCast] using hactiveR
      have hright : abs (abs (record2680Center3212 index)) <
          C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
        simpa [abs_abs] using hleft
      rw [hradiusCast, hposition]
      unfold C1RouteAOwnerScaleAudit.widthBump
      rw [if_pos hleft, if_pos hright]
      congr 1
      rw [div_pow, div_pow, sq_abs]
    dsimp [ratCellBumpInterval3287]
    rw [if_pos hactive]
    simpa [heven] using hmem
  · have hactiveR : ¬ |record2680Center3212 index| <
        (radiusQ : ℝ) := by
      intro h
      apply hactive
      have hp : (positionQ : ℝ) < (radiusQ : ℝ) := by
        rw [hposition]
        exact h
      exact_mod_cast hp
    have hstored : ¬ |record2680Center3212 index| <
        C1RouteAOwnerScaleAudit.storedWidth family ^ 2 := by
      simpa [hradiusCast] using hactiveR
    have hzero : C1RouteAOwnerScaleAudit.widthBump
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2)
        (record2680Center3212 index) = 0 := by
      rw [C1RouteAOwnerScaleAudit.widthBump, if_neg hstored]
    dsimp [ratCellBumpInterval3287]
    rw [if_neg hactive]
    simpa [hzero, RatInterval3276.Mem, RatInterval3276.toReal,
      RealInterval2429.Mem] using
      (show RatInterval3276.Mem (0 : ℝ) ({ lo := 0, hi := 0 } : RatInterval3276) by
        norm_num [RatInterval3276.Mem, RatInterval3276.toReal,
          RealInterval2429.Mem])

end ConnesWeilRH.Dev
