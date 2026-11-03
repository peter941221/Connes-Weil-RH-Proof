import ConnesWeilRH.Dev.C1RouteARationalCellBump3287

namespace ConnesWeilRH.Dev

def ratScaledBumpInterval3298 (t : ℚ) (k : ℕ) : RatInterval3276 :=
  RatInterval3276.mul
    (RatInterval3276.powNat ratBaseInterval3284 60)
    (RatInterval3276.powNat (ratTaylorInterval3283 (t / k)) k)

def ratTailBumpInterval3298 (t : ℚ) : RatInterval3276 :=
  if |t / 8| ≤ (1 : ℚ) then
    ratScaledBumpInterval3298 t 8
  else if (-16 : ℚ) ≤ t then
    ratScaledBumpInterval3298 t 16
  else if (-32 : ℚ) ≤ t then
    ratScaledBumpInterval3298 t 32
  else if (-64 : ℚ) ≤ t then
    ratScaledBumpInterval3298 t 64
  else
    { lo := 0
      hi := (RatInterval3276.powNat ratBaseInterval3284 188).hi }

theorem ratScaledBumpInterval_mem3298
    {radius position t : ℚ} {k : ℕ}
    (hradius : 0 < (radius : ℝ))
    (hposition : 0 ≤ (position : ℝ))
    (hinside : (position : ℝ) < radius)
    (ht : (t : ℝ) = 30 - 30 / (1 - ((position : ℝ) / radius) ^ 2))
    (hk : 0 < k)
    (hscaled : |((t / k : ℚ) : ℝ)| ≤ 1) :
    (ratScaledBumpInterval3298 t k).Mem
      (C1RouteAOwnerScaleAudit.widthBump (radius : ℝ) (position : ℝ)) := by
  apply ratBump_mem_of_scaled_exp_pins3280
    (radius := (radius : ℝ)) (position := (position : ℝ))
    (t := (t : ℝ)) (k := k)
  · exact hradius
  · exact hposition
  · exact hinside
  · exact ht
  · exact hk
  · exact ratBaseInterval_mem3284
  · convert ratTaylorInterval_mem3283 hscaled using 1 <;> norm_num

theorem ratTailBumpInterval_mem3298
    {radius position t : ℚ}
    (hradius : 0 < (radius : ℝ))
    (hposition : 0 ≤ (position : ℝ))
    (hinside : (position : ℝ) < radius)
    (ht : (t : ℝ) = 30 - 30 / (1 - ((position : ℝ) / radius) ^ 2))
    (htnonpos : (t : ℝ) ≤ 0) :
    (ratTailBumpInterval3298 t).Mem
      (C1RouteAOwnerScaleAudit.widthBump (radius : ℝ) (position : ℝ)) := by
  have hbase := ratBaseInterval_mem3284
  have hbase188 := RatInterval3276.mem_powNat hbase 188
  have htQ : t ≤ (0 : ℚ) := by exact_mod_cast htnonpos
  by_cases hsmall : |t / 8| ≤ (1 : ℚ)
  · simp only [ratTailBumpInterval3298, if_pos hsmall]
    have hscale8 : |((t / 8 : ℚ) : ℝ)| ≤ 1 := by
      exact_mod_cast hsmall
    exact ratScaledBumpInterval_mem3298 hradius hposition hinside ht
      (by norm_num) hscale8
  · by_cases h16 : (-16 : ℚ) ≤ t
    · simp only [ratTailBumpInterval3298, if_neg hsmall, if_pos h16]
      have hscale16 : |((t / 16 : ℚ) : ℝ)| ≤ 1 := by
        exact_mod_cast (show |t / 16| ≤ (1 : ℚ) from by
          rw [abs_le]
          constructor <;> linarith)
      exact ratScaledBumpInterval_mem3298 hradius hposition hinside ht
        (by norm_num) hscale16
    · by_cases h32 : (-32 : ℚ) ≤ t
      · simp only [ratTailBumpInterval3298, if_neg hsmall, if_neg h16, if_pos h32]
        have hscale32 : |((t / 32 : ℚ) : ℝ)| ≤ 1 := by
          exact_mod_cast (show |t / 32| ≤ (1 : ℚ) from by
            rw [abs_le]
            constructor <;> linarith)
        exact ratScaledBumpInterval_mem3298 hradius hposition hinside ht
          (by norm_num) hscale32
      · by_cases h64 : (-64 : ℚ) ≤ t
        · simp only [ratTailBumpInterval3298, if_neg hsmall, if_neg h16,
            if_neg h32, if_pos h64]
          have hscale64 : |((t / 64 : ℚ) : ℝ)| ≤ 1 := by
            exact_mod_cast (show |t / 64| ≤ (1 : ℚ) from by
              rw [abs_le]
              constructor <;> linarith)
          exact ratScaledBumpInterval_mem3298 hradius hposition hinside ht
            (by norm_num) hscale64
        · simp only [ratTailBumpInterval3298, if_neg hsmall, if_neg h16,
            if_neg h32, if_neg h64]
          unfold RatInterval3276.Mem RatInterval3276.toReal
            RealInterval2429.Mem
          dsimp
          have hwidth : C1RouteAOwnerScaleAudit.widthBump
              (radius : ℝ) (position : ℝ) =
              Real.exp (-30 : ℝ) * Real.exp (t : ℝ) := by
            rw [C1RouteAOwnerScaleAudit.widthBump, if_pos]
            · rw [← Real.exp_add]
              congr 1
              rw [ht]
              field_simp
              ring
            · rw [abs_of_nonneg hposition]
              exact hinside
          have hexp : Real.exp (-30 : ℝ) * Real.exp (t : ℝ) ≤
              Real.exp (-94 : ℝ) := by
            calc
              Real.exp (-30 : ℝ) * Real.exp (t : ℝ) =
                  Real.exp ((-30 : ℝ) + t) := by rw [← Real.exp_add]
              _ ≤ Real.exp (-94 : ℝ) := by
                apply Real.exp_le_exp.mpr
                have h64Q : t < (-64 : ℚ) := lt_of_not_ge h64
                have h64R : (t : ℝ) < -64 := by exact_mod_cast h64Q
                linarith
          constructor
          · rw [hwidth]
            have hpos : (0 : ℝ) < Real.exp (-30 : ℝ) * Real.exp (t : ℝ) :=
              mul_pos (Real.exp_pos _) (Real.exp_pos _)
            simpa using hpos.le
          · rw [hwidth]
            calc
              Real.exp (-30 : ℝ) * Real.exp (t : ℝ) ≤
                  Real.exp (-94 : ℝ) := hexp
              _ = Real.exp (-1 / 2 : ℝ) ^ 188 := by
                rw [← Real.exp_nat_mul]
                congr 1
                norm_num
              _ ≤ (RatInterval3276.powNat ratBaseInterval3284 188).toReal.hi :=
                hbase188.2

def ratCellBumpInterval3298 (index : ℕ) (family : Fin 30) : RatInterval3276 :=
  let radius := storedWidthRat3287 family ^ 2
  let position := |record2680CenterRat3279 index|
  let t := ratBumpT3286 radius position
  if |record2680CenterRat3279 index| < radius then
    ratTailBumpInterval3298 t
  else
    { lo := 0, hi := 0 }

theorem ratCellBumpInterval_mem3298
    {index : ℕ} (family : Fin 30) (hindex : index < 40960) :
    (ratCellBumpInterval3298 index family).Mem
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
    have hmem := ratTailBumpInterval_mem3298
      (radius := radiusQ) (position := positionQ) (t := tQ)
      hradius hpos hinside ht ht0
    dsimp [ratCellBumpInterval3298]
    rw [if_pos hactive]
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
    dsimp [ratCellBumpInterval3298]
    rw [if_neg hactive]
    simpa [hzero, RatInterval3276.Mem, RatInterval3276.toReal,
      RealInterval2429.Mem] using
      (show RatInterval3276.Mem (0 : ℝ) ({ lo := 0, hi := 0 } : RatInterval3276) by
        norm_num [RatInterval3276.Mem, RatInterval3276.toReal,
          RealInterval2429.Mem])

end ConnesWeilRH.Dev
