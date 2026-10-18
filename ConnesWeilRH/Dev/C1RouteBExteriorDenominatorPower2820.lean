import ConnesWeilRH.Dev.C1RouteBExteriorDistance2819
import ConnesWeilRH.Dev.C1RouteBExteriorMonomialBound2814

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_exterior_denominator_power2820
    {t T y : ℝ} {k : ℕ}
    (hT : 0 < T) (hTy : |y| < T) (hTt : T ≤ t) :
    |t - y|⁻¹ ^ k ≤ (t * (1 - |y| / T))⁻¹ ^ k := by
  have hbase : 0 < t * (1 - |y| / T) := by
    have ht : 0 < t := lt_of_lt_of_le hT hTt
    have hfrac : |y| / T < 1 := (div_lt_one hT).2 hTy
    positivity
  have hdist : t * (1 - |y| / T) ≤ |t - y| :=
    routeB_exterior_distance_lower_bound2819 hT hTt
  have hinv : |t - y|⁻¹ ≤ (t * (1 - |y| / T))⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hbase hdist)
  have hnonneg : 0 ≤ |t - y|⁻¹ := inv_nonneg.mpr (abs_nonneg _)
  exact pow_le_pow_left₀ hnonneg hinv k

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
