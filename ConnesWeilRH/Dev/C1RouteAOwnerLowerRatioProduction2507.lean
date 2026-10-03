import ConnesWeilRH.Dev.C1RouteAOwnerCellLowerRatio2501

/-! Record 2507: production-grid strict lower-ratio domain.

The existing 2488 production endpoint certificate is converted to the
minimum-endpoint ratio used by the corrected 2501 exponential envelope.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem ownerCellLowerRatio_lt_one_of_endpointBounds2507
    {radius step : ℝ} {index : ℕ} (i : Fin 30)
    (hleft : |(-radius + index * step)| < ownerRad_2463 i) :
    ownerCellLowerRatio2501 radius step index i < 1 := by
  by_cases hcroses :
      (-radius + index * step ≤ 0 ∧
        0 ≤ -radius + (index + 1) * step)
  · simp [ownerCellLowerRatio2501, hcroses]
  · rw [show ownerCellLowerRatio2501 radius step index i =
      min |(-radius + index * step)|
          |(-radius + (index + 1) * step)| / ownerRad_2463 i by
        unfold ownerCellLowerRatio2501
        rw [if_neg hcroses]]
    apply (div_lt_iff₀ (ownerRadPos_2465 i)).2
    simpa only [one_mul] using
      (lt_of_le_of_lt (min_le_left _ _) hleft)

theorem ownerCellLowerRatio_lt_one_production2507
    {index : ℕ} (hlo : 196 ≤ index) (hhi : index ≤ 443)
    (i : Fin 30) :
    ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) index i < 1 := by
  have hs := (ownerCellSafeEndpoint_true_iff2488
    stripRadius2303 (stripRadius2303 / 320) index).mp
    (ownerCellSafeEndpoint_production2488 hlo hhi)
  exact ownerCellLowerRatio_lt_one_of_endpointBounds2507 i (hs i).1

end ConnesWeilRH.Dev
