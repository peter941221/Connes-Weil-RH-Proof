import ConnesWeilRH.Dev.C1RouteARationalTaylor3283

namespace ConnesWeilRH.Dev

def ratBaseInterval3284 : RatInterval3276 :=
  ratTaylorInterval3283 (-1 / 2 : ℚ)

def ratCentralBumpInterval3284 (t : ℚ) : RatInterval3276 :=
  RatInterval3276.mul
    (RatInterval3276.powNat ratBaseInterval3284 60)
    (RatInterval3276.powNat (ratTaylorInterval3283 (t / 8)) 8)

theorem ratBaseInterval_mem3284 :
    ratBaseInterval3284.Mem (Real.exp (-1 / 2 : ℝ)) := by
  unfold ratBaseInterval3284
  have h := ratTaylorInterval_mem3283 (x := (-1 / 2 : ℚ)) (by norm_num)
  convert h using 1 <;> norm_num

theorem ratCentralBumpInterval_mem3284
    {radius position t : ℚ}
    (hradius : 0 < (radius : ℝ))
    (hposition : 0 ≤ (position : ℝ))
    (hinside : (position : ℝ) < radius)
    (ht : (t : ℝ) = 30 - 30 / (1 - ((position : ℝ) / radius) ^ 2))
    (hscaled : |((t / 8 : ℚ) : ℝ)| ≤ 1) :
    (ratCentralBumpInterval3284 t).Mem
      (C1RouteAOwnerScaleAudit.widthBump (radius : ℝ) (position : ℝ)) := by
  have hadd := ratTaylorInterval_mem3283
    (x := t / 8) hscaled
  have hadd' : (ratTaylorInterval3283 (t / 8)).Mem
      (Real.exp ((t : ℝ) / 8)) := by
    convert hadd using 1 <;> norm_num
  have hmain := ratBump_mem_of_scaled_exp_pins3280
    (radius := (radius : ℝ)) (position := (position : ℝ))
    (t := (t : ℝ)) (k := 8)
    (base := ratBaseInterval3284)
    (addend := ratTaylorInterval3283 (t / 8))
    hradius hposition hinside ht (by norm_num)
    ratBaseInterval_mem3284 hadd'
  exact hmain

end ConnesWeilRH.Dev