import ConnesWeilRH.Dev.C1RouteARationalSignedComplex3331
import ConnesWeilRH.Dev.C1RouteARationalSignedJetEndpointDecomp3323

namespace ConnesWeilRH.Dev

theorem ratCoefficientRect3282_family4_signs3332 :
    (ratCoefficientRect3282 4).reHi < 0 ∧
      (ratCoefficientRect3282 4).imHi < 0 := by
  norm_num [ratCoefficientRect3282, Matrix.cons_val_four]

theorem ratWeightedPhysicalTermRect3310_family4_reHi_signed3332
    (cell : ℕ)
    (hre : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reHi)
    (him : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imHi) :
    (ratWeightedPhysicalTermRect3310 2 cell 4).reHi =
      ((ratCoefficientRect3282 4).reHi *
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell 4)
            (ratWeightedUnitJetRect3310 2 1 cell 4))
          (ratWeightedUnitJetRect3310 2 2 cell 4)).reLo) -
      ((ratCoefficientRect3282 4).imHi *
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell 4)
            (ratWeightedUnitJetRect3310 2 1 cell 4))
          (ratWeightedUnitJetRect3310 2 2 cell 4)).imHi) := by
  rw [ratWeightedPhysicalTermRect3310_order2_eq]
  have hcoef : ratCoefficientRect3282 4 =
      ({ reLo := -(6001732121601251 : ℚ) / 32,
         reHi := -(6001732121601251 : ℚ) / 32,
         imLo := -(6739580861423611 : ℚ) / 128,
         imHi := -(6739580861423611 : ℚ) / 128 } : RatRect3276) := by
    norm_num [ratCoefficientRect3282, Matrix.cons_val_four]
  rw [hcoef]
  change (RatRect3276.mul
      ({ reLo := (ratCoefficientRect3282 4).reHi,
         reHi := (ratCoefficientRect3282 4).reHi,
         imLo := (ratCoefficientRect3282 4).imHi,
         imHi := (ratCoefficientRect3282 4).imHi } : RatRect3276)
      _).reHi = _
  rw [ratRect_mul_singleton_reHi_formula3331]
  have hsign := ratCoefficientRect3282_family4_signs3332
  rw [max_eq_left]
  · rw [min_eq_right]
    · rfl
    · exact mul_le_mul_of_nonpos_left him hsign.2.le
  · exact mul_le_mul_of_nonpos_left
      hre hsign.1.le

theorem ratWeightedPhysicalTermRect3310_cell0_order2_family4_reHi_signed3332 :
    (ratWeightedPhysicalTermRect3310 2 0 4).reHi =
      ((ratCoefficientRect3282 4).reHi *
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4)).reLo) -
      ((ratCoefficientRect3282 4).imHi *
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4)).imHi) := by
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
  have hre :
      (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4)).reLo ≤
      (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4)).reHi := by
    simp [RatRect3276.add]
    linarith [h0re, h1re, h2re]
  have him :
      (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4)).imLo ≤
      (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 0 4)
            (ratWeightedUnitJetRect3310 2 1 0 4))
          (ratWeightedUnitJetRect3310 2 2 0 4)).imHi := by
    simp [RatRect3276.add]
    linarith [h0im, h1im, h2im]
  exact ratWeightedPhysicalTermRect3310_family4_reHi_signed3332 0 hre him

theorem ratWeightedPhysicalTermRect3310_family4_reHi_le_of_signed_certificate3332
    (cell : ℕ)
    (hactive : |record2680Center3212 cell| <
      C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2)
    (hre : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).reHi)
    (him : (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imLo ≤
      (RatRect3276.add
        (RatRect3276.add
          (ratWeightedUnitJetRect3310 2 0 cell 4)
          (ratWeightedUnitJetRect3310 2 1 cell 4))
        (ratWeightedUnitJetRect3310 2 2 cell 4)).imHi)
    (hbound :
      ((ratCoefficientRect3282 4).reHi *
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell 4)
            (ratWeightedUnitJetRect3310 2 1 cell 4))
          (ratWeightedUnitJetRect3310 2 2 cell 4)).reLo) -
      ((ratCoefficientRect3282 4).imHi *
        (RatRect3276.add
          (RatRect3276.add
            (ratWeightedUnitJetRect3310 2 0 cell 4)
            (ratWeightedUnitJetRect3310 2 1 cell 4))
          (ratWeightedUnitJetRect3310 2 2 cell 4)).imHi) ≤
      1 / 10 ^ 14) :
    (ratWeightedPhysicalTermRect3310 2 cell 4).reHi ≤ 1 / 10 ^ 14 := by
  exact (ratWeightedPhysicalTermRect3310_family4_reHi_signed3332
    cell hre him).le.trans hbound

end ConnesWeilRH.Dev
