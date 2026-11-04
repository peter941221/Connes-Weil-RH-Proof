import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3328
import ConnesWeilRH.Dev.C1RouteARationalSignedJetEndpointDecomp3323

namespace ConnesWeilRH.Dev

def ratRectEndpointAbsBoundOfUnitJet3327
    (order index cell : ℕ) (family : Fin 30) : ℚ :=
  ratRectEndpointAbsBound3326
    (ratWeightedUnitJetRect3310 order index cell family)

set_option maxHeartbeats 10000000 in
theorem ratWeightedPhysicalTermRect3310_order2_reHi_le_abs_bound3329
    (cell : ℕ) (family : Fin 30) :
    (ratWeightedPhysicalTermRect3310 2 cell family).reHi ≤
      2 * ratRectEndpointAbsBound3326 (ratCoefficientRect3282 family) *
        (ratRectEndpointAbsBound3326
          (ratWeightedUnitJetRect3310 2 0 cell family) +
          ratRectEndpointAbsBound3326
            (ratWeightedUnitJetRect3310 2 1 cell family) +
          ratRectEndpointAbsBound3326
            (ratWeightedUnitJetRect3310 2 2 cell family)) := by
  rw [ratWeightedPhysicalTermRect3310_order2_eq]
  have hmul := ratRect_mul_reHi_le_abs_bound3326
    (ratCoefficientRect3282 family)
    (RatRect3276.add
      (RatRect3276.add
        (ratWeightedUnitJetRect3310 2 0 cell family)
        (ratWeightedUnitJetRect3310 2 1 cell family))
      (ratWeightedUnitJetRect3310 2 2 cell family))
  have hadd := ratRect_add_endpointAbsBound_le_sum3328
    (RatRect3276.add
      (ratWeightedUnitJetRect3310 2 0 cell family)
      (ratWeightedUnitJetRect3310 2 1 cell family))
    (ratWeightedUnitJetRect3310 2 2 cell family)
  have hadd01 := ratRect_add_endpointAbsBound_le_sum3328
    (ratWeightedUnitJetRect3310 2 0 cell family)
    (ratWeightedUnitJetRect3310 2 1 cell family)
  have hsum : ratRectEndpointAbsBound3326
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell family)
          (ratWeightedUnitJetRect3310 2 1 cell family))
        (ratWeightedUnitJetRect3310 2 2 cell family)) ≤
      ratRectEndpointAbsBound3326
        (ratWeightedUnitJetRect3310 2 0 cell family) +
      ratRectEndpointAbsBound3326
        (ratWeightedUnitJetRect3310 2 1 cell family) +
      ratRectEndpointAbsBound3326
        (ratWeightedUnitJetRect3310 2 2 cell family) := by
    linarith
  exact le_trans hmul (by
    apply mul_le_mul_of_nonneg_left hsum
    exact mul_nonneg (by norm_num)
      (ratRectEndpointAbsBound3326_nonneg (ratCoefficientRect3282 family)))

end ConnesWeilRH.Dev
