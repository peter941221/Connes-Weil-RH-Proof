import ConnesWeilRH.Dev.C1RouteARationalBumpEndpoint3337

namespace ConnesWeilRH.Dev

theorem ratRect_mul_real_reLo_le_zero_of_zero_lo3338
    (a : RatRect3276) (b : RatInterval3276)
    (hbLo : b.lo = 0) :
    (RatRect3276.mul a (ratRealRect3281 b)).reLo ≤ 0 := by
  unfold RatRect3276.mul RatInterval3276.mul RatInterval3276.sub
    ratRealRect3281
  dsimp
  have hreal :
      min (min (a.reLo * b.lo) (a.reLo * b.hi))
          (min (a.reHi * b.lo) (a.reHi * b.hi)) ≤ 0 := by
    rw [hbLo]
    calc
      min (min (a.reLo * 0) (a.reLo * b.hi))
          (min (a.reHi * 0) (a.reHi * b.hi)) ≤
          min (a.reLo * 0) (a.reLo * b.hi) := min_le_left _ _
      _ ≤ a.reLo * 0 := min_le_left _ _
      _ = 0 := mul_zero _
  have himag :
      max (max (a.imLo * 0) (a.imLo * 0))
          (max (a.imHi * 0) (a.imHi * 0)) = 0 := by
    simp
  rw [himag]
  simpa using hreal

theorem signed_jet_endpoint3338_cell0_order2_index0_reLo_le_zero :
    (ratWeightedUnitJetRect3310 2 0 0 4).reLo ≤ 0 := by
  unfold ratWeightedUnitJetRect3310
  rw [show ratRectPowNat3310 (ratWeightedLambdaRect3310 4) 0 =
      ratScalarRect3310 1 by rfl]
  simp only [ratScalarRect3310, ratRectPowNat3310]
  apply ratRect_mul_real_reLo_le_zero_of_zero_lo3338
  exact signed_bump_endpoint3337_cell0_order2_family4_reLo_eq_zero

end ConnesWeilRH.Dev
