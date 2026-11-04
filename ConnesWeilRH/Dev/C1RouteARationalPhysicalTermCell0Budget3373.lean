import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermBudget3370
import ConnesWeilRH.Dev.C1RouteARationalImaginaryEndpointBudget3371
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetAbsBudget3372

namespace ConnesWeilRH.Dev

def ratWeightedJetSumRect_cell0_order2_family4_3373 : RatRect3276 :=
  RatRect3276.add
    (RatRect3276.add
      (ratWeightedUnitJetRect3310 2 0 0 4)
      (ratWeightedUnitJetRect3310 2 1 0 4))
    (ratWeightedUnitJetRect3310 2 2 0 4)

theorem ratWeightedJetSumRect_cell0_order2_family4_ordered3373 :
    (ratWeightedJetSumRect_cell0_order2_family4_3373).reLo ≤
      (ratWeightedJetSumRect_cell0_order2_family4_3373).reHi ∧
    (ratWeightedJetSumRect_cell0_order2_family4_3373).imLo ≤
      (ratWeightedJetSumRect_cell0_order2_family4_3373).imHi := by
  have hactive : |record2680Center3212 0| <
      C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
    have h : |record2680CenterRat3279 0| < storedWidthRat3287 4 ^ 2 := by
      norm_num [record2680CenterRat3279, storedWidthRat3287,
        Matrix.cons_val_four]
    have hc := record2680CenterRat_cast3279 0
    have hr : ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) =
        C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
      norm_num [Rat.cast_pow, storedWidthRat_cast3287]
    rw [← hc, ← hr]
    exact_mod_cast h
  have hmem (index : ℕ) (hindex : index < 3) :
      (ratWeightedUnitJetRect3310 2 index 0 4).Mem
        ((Nat.choose 2 index : ℂ) *
          iteratedDeriv index
            (weightedPhase2537 (-1 / 2) (capturedModulations2584 4))
            (record2680Center3212 0) *
          (iteratedDeriv (2 - index)
            (C1RouteAOwnerScaleAudit.widthBump
              (C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2))
            (record2680Center3212 0) : ℝ)) := by
    apply ratWeightedUnitJetRect_mem3310 (by norm_num) (by omega) (by norm_num) 4
  have h0 := hmem 0 (by norm_num)
  have h1 := hmem 1 (by norm_num)
  have h2 := hmem 2 (by norm_num)
  have h0re :
      (ratWeightedUnitJetRect3310 2 0 0 4).reLo ≤
        (ratWeightedUnitJetRect3310 2 0 0 4).reHi := by
    have h := h0.1.trans h0.2.1
    change ((ratWeightedUnitJetRect3310 2 0 0 4).reLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 0 0 4).reHi at h
    exact_mod_cast h
  have h1re :
      (ratWeightedUnitJetRect3310 2 1 0 4).reLo ≤
        (ratWeightedUnitJetRect3310 2 1 0 4).reHi := by
    have h := h1.1.trans h1.2.1
    change ((ratWeightedUnitJetRect3310 2 1 0 4).reLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 1 0 4).reHi at h
    exact_mod_cast h
  have h2re :
      (ratWeightedUnitJetRect3310 2 2 0 4).reLo ≤
        (ratWeightedUnitJetRect3310 2 2 0 4).reHi := by
    have h := h2.1.trans h2.2.1
    change ((ratWeightedUnitJetRect3310 2 2 0 4).reLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 2 0 4).reHi at h
    exact_mod_cast h
  have h0im :
      (ratWeightedUnitJetRect3310 2 0 0 4).imLo ≤
        (ratWeightedUnitJetRect3310 2 0 0 4).imHi := by
    have h := h0.2.2.1.trans h0.2.2.2
    change ((ratWeightedUnitJetRect3310 2 0 0 4).imLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 0 0 4).imHi at h
    exact_mod_cast h
  have h1im :
      (ratWeightedUnitJetRect3310 2 1 0 4).imLo ≤
        (ratWeightedUnitJetRect3310 2 1 0 4).imHi := by
    have h := h1.2.2.1.trans h1.2.2.2
    change ((ratWeightedUnitJetRect3310 2 1 0 4).imLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 1 0 4).imHi at h
    exact_mod_cast h
  have h2im :
      (ratWeightedUnitJetRect3310 2 2 0 4).imLo ≤
        (ratWeightedUnitJetRect3310 2 2 0 4).imHi := by
    have h := h2.2.2.1.trans h2.2.2.2
    change ((ratWeightedUnitJetRect3310 2 2 0 4).imLo : ℝ) ≤
      (ratWeightedUnitJetRect3310 2 2 0 4).imHi at h
    exact_mod_cast h
  constructor
  · unfold ratWeightedJetSumRect_cell0_order2_family4_3373
    simp [RatRect3276.add]
    linarith
  · unfold ratWeightedJetSumRect_cell0_order2_family4_3373
    simp [RatRect3276.add]
    linarith

theorem ratWeightedPhysicalTermRect_cell0_order2_family4_reHi_le3373 :
    (ratWeightedPhysicalTermRect3310 2 0 4).reHi ≤ 7 := by
  have hordered := ratWeightedJetSumRect_cell0_order2_family4_ordered3373
  have hreal0 := ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell0_order2_family4_3373)
  have himag0 := ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (ratWeightedJetSumRect_cell0_order2_family4_3373)
  have hbudget := ratWeightedUnitJetSumRect_cell0_order2_family4_endpointAbs_le3372
  have hreal : ratRectRealEndpointAbsBound3342
      (ratWeightedJetSumRect_cell0_order2_family4_3373) ≤ 27 / 10 ^ 15 :=
    hreal0.trans hbudget
  have himag : ratRectImagEndpointAbsBound3342
      (ratWeightedJetSumRect_cell0_order2_family4_3373) ≤ 27 / 10 ^ 15 :=
    himag0.trans hbudget
  exact le_trans
    (ratWeightedPhysicalTermRect3310_family4_reHi_le_of_coordinate_budgets3370
      0 hordered.1 hordered.2 (27 / 10 ^ 15) (27 / 10 ^ 15) hreal himag)
    (by norm_num [ratCoefficientRect3282, Matrix.cons_val_four])

end ConnesWeilRH.Dev
