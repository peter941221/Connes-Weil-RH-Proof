import ConnesWeilRH.Dev.C1RouteARationalBump3284

namespace ConnesWeilRH.Dev

def ratTailBumpInterval3285 : RatInterval3276 :=
  { lo := 0
    hi := (RatInterval3276.powNat ratBaseInterval3284 76).hi }

theorem ratTailBumpInterval_mem3285
    {radius position t : ℚ}
    (hradius : 0 < (radius : ℝ))
    (hposition : 0 ≤ (position : ℝ))
    (hinside : (position : ℝ) < radius)
    (ht : (t : ℝ) ≤ -8)
    (heq : (t : ℝ) = 30 - 30 / (1 - ((position : ℝ) / radius) ^ 2)) :
    ratTailBumpInterval3285.Mem
      (C1RouteAOwnerScaleAudit.widthBump (radius : ℝ) (position : ℝ)) := by
  have hbase := ratBaseInterval_mem3284
  have hbasepow := RatInterval3276.mem_powNat hbase 76
  have hexp38 : Real.exp (-38 : ℝ) = Real.exp (-1 / 2 : ℝ) ^ 76 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hexp_t : Real.exp (t : ℝ) ≤ Real.exp (-8 : ℝ) :=
    Real.exp_le_exp.mpr ht
  have hupper38 : Real.exp (-30 : ℝ) * Real.exp (t : ℝ) ≤
      Real.exp (-38 : ℝ) := by
    calc
      Real.exp (-30 : ℝ) * Real.exp (t : ℝ) ≤
          Real.exp (-30 : ℝ) * Real.exp (-8 : ℝ) :=
        mul_le_mul_of_nonneg_left hexp_t (Real.exp_nonneg _)
      _ = Real.exp (-38 : ℝ) := by
        rw [← Real.exp_add]
        norm_num
  have hwidth : C1RouteAOwnerScaleAudit.widthBump (radius : ℝ) (position : ℝ) =
      Real.exp (-30 : ℝ) * Real.exp (t : ℝ) := by
    rw [C1RouteAOwnerScaleAudit.widthBump, if_pos]
    · rw [← Real.exp_add]
      congr 1
      rw [heq]
      field_simp
      ring
    · rw [abs_of_nonneg hposition]
      exact hinside
  unfold ratTailBumpInterval3285 RatInterval3276.Mem
    RatInterval3276.toReal RealInterval2429.Mem
  dsimp
  constructor
  · rw [hwidth]
    norm_num
    positivity
  · rw [hwidth]
    calc
      Real.exp (-30 : ℝ) * Real.exp (t : ℝ) ≤ Real.exp (-38 : ℝ) := hupper38
      _ = Real.exp (-1 / 2 : ℝ) ^ 76 := hexp38
      _ ≤ (RatInterval3276.powNat ratBaseInterval3284 76).toReal.hi := by
        exact hbasepow.2
end ConnesWeilRH.Dev