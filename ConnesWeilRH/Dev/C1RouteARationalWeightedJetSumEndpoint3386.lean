import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3381
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3383
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetEndpoint3385

namespace ConnesWeilRH.Dev

def ratWeightedJetSumRect_cell1_order2_family4_3386 : RatRect3276 :=
  RatRect3276.add
    (RatRect3276.add
      (ratWeightedUnitJetRect3310 2 0 1 4)
      (ratWeightedUnitJetRect3310 2 1 1 4))
    (ratWeightedUnitJetRect3310 2 2 1 4)

theorem ratWeightedJetSumRect_cell1_order2_family4_ordered3386 :
    (ratWeightedJetSumRect_cell1_order2_family4_3386).reLo ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3386).reHi ∧
    (ratWeightedJetSumRect_cell1_order2_family4_3386).imLo ≤
      (ratWeightedJetSumRect_cell1_order2_family4_3386).imHi := by
  have hmem (index : ℕ) (hindex : index < 3) :
      (ratWeightedUnitJetRect3310 2 index 1 4).Mem
        ((Nat.choose 2 index : ℂ) *
          iteratedDeriv index
            (weightedPhase2537 (-1 / 2) (capturedModulations2584 4))
            (record2680Center3212 1) *
          (iteratedDeriv (2 - index)
            (C1RouteAOwnerScaleAudit.widthBump
              (C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2))
            (record2680Center3212 1) : ℝ)) := by
    apply ratWeightedUnitJetRect_mem3310 (by norm_num) (by omega) (by norm_num) 4
  have h0 := hmem 0 (by norm_num)
  have h1 := hmem 1 (by norm_num)
  have h2 := hmem 2 (by norm_num)
  have h0re := h0.1.trans h0.2.1
  have h1re := h1.1.trans h1.2.1
  have h2re := h2.1.trans h2.2.1
  have h0im := h0.2.2.1.trans h0.2.2.2
  have h1im := h1.2.2.1.trans h1.2.2.2
  have h2im := h2.2.2.1.trans h2.2.2.2
  change ((ratWeightedUnitJetRect3310 2 0 1 4).reLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 0 1 4).reHi at h0re
  change ((ratWeightedUnitJetRect3310 2 1 1 4).reLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 1 1 4).reHi at h1re
  change ((ratWeightedUnitJetRect3310 2 2 1 4).reLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 2 1 4).reHi at h2re
  change ((ratWeightedUnitJetRect3310 2 0 1 4).imLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 0 1 4).imHi at h0im
  change ((ratWeightedUnitJetRect3310 2 1 1 4).imLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 1 1 4).imHi at h1im
  change ((ratWeightedUnitJetRect3310 2 2 1 4).imLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 2 1 4).imHi at h2im
  constructor
  · unfold ratWeightedJetSumRect_cell1_order2_family4_3386
    simp [RatRect3276.add]
    exact_mod_cast add_le_add (add_le_add h0re h1re) h2re
  · unfold ratWeightedJetSumRect_cell1_order2_family4_3386
    simp [RatRect3276.add]
    exact_mod_cast add_le_add (add_le_add h0im h1im) h2im

theorem ratWeightedJetSumRect_cell1_order2_family4_reHi_le3386 :
    (ratWeightedJetSumRect_cell1_order2_family4_3386).reHi ≤
      7 / 10 ^ 15 := by
  unfold ratWeightedJetSumRect_cell1_order2_family4_3386
  simp [RatRect3276.add]
  linarith [
    signed_jet_endpoint3381_cell1_order2_index0_family4_reHi_le,
    signed_jet_endpoint3383_cell1_order2_index1_family4_reHi_le,
    signed_jet_endpoint3385_cell1_order2_index2_family4_reHi_le]

end ConnesWeilRH.Dev
