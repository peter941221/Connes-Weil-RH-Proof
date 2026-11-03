import ConnesWeilRH.Dev.C1RouteARationalFamily3282

namespace ConnesWeilRH.Dev

def ratTaylorSum3283 (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range 30, x ^ m / (m.factorial : ℚ)

def ratTaylorError3283 (x : ℚ) : ℚ :=
  |x| ^ 30 * ((31 : ℚ) / ((30 : ℕ).factorial * 30))

def ratTaylorInterval3283 (x : ℚ) : RatInterval3276 :=
  { lo := ratTaylorSum3283 x - ratTaylorError3283 x
    hi := ratTaylorSum3283 x + ratTaylorError3283 x }

theorem ratTaylorInterval_mem3283
    {x : ℚ} (hx : |(x : ℝ)| ≤ 1) :
    (ratTaylorInterval3283 x).Mem (Real.exp (x : ℝ)) := by
  have hS : ∑ m ∈ Finset.range 30,
      (x : ℝ) ^ m / (m.factorial : ℝ) =
      (ratTaylorSum3283 x : ℝ) := by
    simp [ratTaylorSum3283, Rat.cast_sum, Rat.cast_add, Rat.cast_sub,
      Rat.cast_mul, Rat.cast_div, Rat.cast_pow]
  have hE : |(x : ℝ)| ^ 30 *
      ((30 : ℕ).succ / ((30 : ℕ).factorial * 30)) =
      (ratTaylorError3283 x : ℝ) := by
    simp [ratTaylorError3283, Rat.cast_abs, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow]
  have hpin := expTwoSided2676 (n := 30) (by norm_num) hx hS hE
  unfold RatInterval3276.Mem RatInterval3276.toReal
  unfold ratTaylorInterval3283
  unfold RealInterval2429.Mem
  dsimp
  simpa only [Rat.cast_sub, Rat.cast_add] using hpin

end ConnesWeilRH.Dev