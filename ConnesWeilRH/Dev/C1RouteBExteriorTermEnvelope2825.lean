import ConnesWeilRH.Dev.C1RouteBCabsEnvelope2824
import ConnesWeilRH.Dev.C1RouteBExteriorDenominatorPower2820

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_exterior_term_envelope2825
    {y Y Q L S t T : ℝ} {k : ℕ}
    (hy : 0 ≤ Y) (hS : 0 < S) (hL : 0 < L)
    (hyY : |y| ≤ Y) (hLQ : L ≤ |Q|)
    (hT : 0 < T) (hTy : |y| < T) (hTt : T ≤ t)
    {C R : ℝ} (hC : 0 ≤ C)
    (hCabs : Y / (S * L) ≤ C)
    (hRpow : (t * (1 - |y| / T))⁻¹ ^ k ≤ R) :
    |y| / (S * |Q|) * |t - y|⁻¹ ^ k ≤ C * R := by
  have hcabs := routeB_cabs_envelope2824 hy hS hL hyY hLQ
  have hden := routeB_exterior_denominator_power2820 (k := k) hT hTy hTt
  have hc : |y| / (S * |Q|) ≤ C := le_trans hcabs hCabs
  have hd : |t - y|⁻¹ ^ k ≤ R := le_trans hden hRpow
  exact mul_le_mul hc hd (by positivity) hC

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
