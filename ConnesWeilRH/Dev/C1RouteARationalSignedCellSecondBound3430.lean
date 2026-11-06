import ConnesWeilRH.Dev.C1RouteARationalPhysicalTermTightEndpoint3429
import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCellLocalJets3224

namespace ConnesWeilRH.Dev

open scoped BigOperators

noncomputable def signedCellFamilyCertificate3430 (familyUpper : Fin 30 → ℝ) : Fin 30 → ℝ :=
  fun family => if family = 4 then 1 / 100 else familyUpper family

theorem record2680_cell_second_bound_signed3430
    (familyUpper : Fin 30 → ℝ)
    (hfamily4 :
      (record2680CorrectionCoefficient 4 *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
          (record2680Center3212 1)).re ≤ 1 / 100)
    (hrest : ∀ family : Fin 30, family ≠ 4 →
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re ≤ familyUpper family) :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 1) ≤
      ∑ family : Fin 30, signedCellFamilyCertificate3430 familyUpper family := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  rw [iteratedDeriv_re_eq_re_iteratedDeriv3220
    (weightedPhysical2539 (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584) 2 (record2680Center3212 1)
    (weightedPhysical2539_contDiff (-1 / 2) record2680CorrectionCoefficient
      capturedModulations2584)]
  rw [weightedPhysical2539_iteratedDeriv]
  change (∑ family : Fin 30,
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re) ≤ _
  apply Finset.sum_le_sum
  intro family hmem
  by_cases hfamily : family = 4
  · subst hfamily
    have hmem4 : (ratWeightedPhysicalTermRect3310 2 1 4).Mem
        (record2680CorrectionCoefficient 4 *
          weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
            (record2680Center3212 1)) := by
      apply RatRect3276.mem_mul
      · exact ratCoefficientRect_mem3282 4
      · exact ratWeightedUnitJetSumRect_mem3310 (by norm_num) (by norm_num) 4
    have hrect :
        (record2680CorrectionCoefficient 4 *
          weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
            (record2680Center3212 1)).re ≤
        ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) := hmem4.2.1
    have htight := ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3429
    have hq : (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ (1 / 100 : ℚ) := htight
    have hqR0 : ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) ≤
        ((1 / 100 : ℚ) : ℝ) := by
      exact_mod_cast hq
    have hqR : ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) ≤
        (1 / 100 : ℝ) := by
      norm_num at hqR0 ⊢
      exact hqR0
    have hbound :
        (record2680CorrectionCoefficient 4 *
          weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
            (record2680Center3212 1)).re ≤ (1 / 100 : ℝ) :=
      hrect.trans hqR
    simpa [signedCellFamilyCertificate3430] using hbound
  · simpa [signedCellFamilyCertificate3430, hfamily] using hrest family hfamily

theorem record2680_cell_second_bound_signed3430_from3429
    (familyUpper : Fin 30 → ℝ)
    (hrest : ∀ family : Fin 30, family ≠ 4 →
      (record2680CorrectionCoefficient family *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 family
          (record2680Center3212 1)).re ≤ familyUpper family) :
    iteratedDeriv 2
      (weightedExternal3201 (-1 / 2) record2680CorrectionCoefficient
        capturedModulations2584) (record2680Center3212 1) ≤
      ∑ family : Fin 30, signedCellFamilyCertificate3430 familyUpper family := by
  apply record2680_cell_second_bound_signed3430 familyUpper
  · have hmem4 : (ratWeightedPhysicalTermRect3310 2 1 4).Mem
        (record2680CorrectionCoefficient 4 *
          weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
            (record2680Center3212 1)) := by
      apply RatRect3276.mem_mul
      · exact ratCoefficientRect_mem3282 4
      · exact ratWeightedUnitJetSumRect_mem3310 (by norm_num) (by norm_num) 4
    have hrect := hmem4.2.1
    change (record2680CorrectionCoefficient 4 *
        weightedUnitJet2539 2 (-1 / 2) capturedModulations2584 4
          (record2680Center3212 1)).re ≤
      ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) at hrect
    have htight := ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3429
    have hq : (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ (1 / 100 : ℚ) := htight
    have hqR0 : ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) ≤
        ((1 / 100 : ℚ) : ℝ) := by
      exact_mod_cast hq
    have hqR : ((ratWeightedPhysicalTermRect3310 2 1 4).reHi : ℝ) ≤
        (1 / 100 : ℝ) := by
      norm_num at hqR0 ⊢
      exact hqR0
    exact hrect.trans hqR
  · exact hrest

end ConnesWeilRH.Dev
