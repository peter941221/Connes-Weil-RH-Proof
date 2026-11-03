import ConnesWeilRH.Dev.C1RouteARationalPhase3279

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

 theorem ratBump_mem_of_scaled_exp_pins3280
    {radius position t : ℝ} {k : ℕ}
    {base addend : RatInterval3276}
    (hradius : 0 < radius)
    (hposition : 0 ≤ position)
    (hinside : position < radius)
    (ht : t = 30 - 30 / (1 - (position / radius) ^ 2))
    (hk : 0 < k)
    (hbase : base.Mem (Real.exp (-1 / 2 : ℝ)))
    (haddend : addend.Mem (Real.exp (t / k))) :
    (RatInterval3276.mul (RatInterval3276.powNat base 60)
      (RatInterval3276.powNat addend k)).Mem
      (widthBump radius position) := by
  have hbasepow := RatInterval3276.mem_powNat hbase 60
  have haddpow := RatInterval3276.mem_powNat haddend k
  have hmul := RatInterval3276.mem_mul hbasepow haddpow
  have hexpbase : Real.exp (-30 : ℝ) = Real.exp (-1 / 2 : ℝ) ^ 60 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hexpadd : Real.exp t = Real.exp (t / k) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hwidth : widthBump radius position =
      Real.exp (-30 : ℝ) * Real.exp t := by
    rw [widthBump, if_pos]
    · rw [← Real.exp_add]
      congr 1
      rw [ht]
      field_simp
      ring
    · rw [abs_of_nonneg hposition]
      exact hinside
  rw [hwidth, hexpbase, hexpadd]
  exact hmul

end ConnesWeilRH.Dev