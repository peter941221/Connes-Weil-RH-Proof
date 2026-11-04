import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310

namespace ConnesWeilRH.Dev

theorem ratWeightedPhysicalTermRect3310_eq_zero_of_inactive
    (order cell : ℕ) (family : Fin 30)
    (hinactive : ¬ |record2680CenterRat3279 cell| < storedWidthRat3287 family ^ 2) :
    ratWeightedPhysicalTermRect3310 order cell family =
      ({ reLo := 0, reHi := 0, imLo := 0, imHi := 0 } : RatRect3276) := by
  have hterm : ∀ index : ℕ,
      ratWeightedUnitJetRect3310 order index cell family =
        ({ reLo := 0, reHi := 0, imLo := 0, imHi := 0 } : RatRect3276) := by
    intro index
    unfold ratWeightedUnitJetRect3310 ratBumpRect3310 ratBumpJetInterval3310
    rw [if_neg hinactive, ratRect_mul_zero_real3288]
  have hsum : ratWeightedUnitJetSumRect3310 order cell family =
      ({ reLo := 0, reHi := 0, imLo := 0, imHi := 0 } : RatRect3276) := by
    simp [ratWeightedUnitJetSumRect3310, RatRect3276.sumFinset, hterm]
  unfold ratWeightedPhysicalTermRect3310
  rw [hsum]
  simpa [ratRealRect3281] using
    ratRect_mul_zero_real3288 (ratCoefficientRect3282 family)

theorem ratWeightedPhysicalTermRect3310_reHi_eq_zero_of_inactive
    (order cell : ℕ) (family : Fin 30)
    (hinactive : ¬ |record2680CenterRat3279 cell| < storedWidthRat3287 family ^ 2) :
    (ratWeightedPhysicalTermRect3310 order cell family).reHi = 0 := by
  rw [ratWeightedPhysicalTermRect3310_eq_zero_of_inactive order cell family hinactive]

theorem ratWeightedPhysicalTermRect3310_cell0_family0_reHi (order : ℕ) :
    (ratWeightedPhysicalTermRect3310 order 0 0).reHi = 0 := by
  apply ratWeightedPhysicalTermRect3310_reHi_eq_zero_of_inactive
  norm_num [record2680CenterRat3279, storedWidthRat3287]

theorem ratWeightedPhysicalTermRect3310_cell0_family4_active :
    |record2680CenterRat3279 0| < storedWidthRat3287 4 ^ 2 := by
  norm_num [record2680CenterRat3279, storedWidthRat3287, Matrix.cons_val_four]

theorem ratWeightedPhaseRect3310_cell0_family4_mem :
    (ratWeightedPhaseRect3310 0 4).Mem
      (weightedPhase2537 (-1 / 2) (capturedModulations2584 4)
        (record2680Center3212 0)) := by
  apply ratWeightedPhaseRect_mem3310 (by norm_num) 4
  have hq := ratWeightedPhysicalTermRect3310_cell0_family4_active
  have hcenter :
      (record2680CenterRat3279 0 : ℝ) = record2680Center3212 0 :=
    record2680CenterRat_cast3279 0
  have hradius :
      ((storedWidthRat3287 4 ^ 2 : ℚ) : ℝ) =
        C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2 := by
    norm_num [Rat.cast_pow, storedWidthRat_cast3287]
  rw [← hcenter, ← hradius]
  exact_mod_cast hq

theorem ratBumpRect3310_order2_cell0_family4_mem :
    (ratBumpRect3310 2 0 4).Mem
      ((iteratedDeriv 2
        (C1RouteAOwnerScaleAudit.widthBump
          (C1RouteAOwnerScaleAudit.storedWidth 4 ^ 2))
        (record2680Center3212 0) : ℝ) : ℂ) := by
  apply ratBumpRect_mem3310 (by norm_num) 4

end ConnesWeilRH.Dev
