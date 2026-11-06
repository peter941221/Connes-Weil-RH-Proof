import ConnesWeilRH.Dev.C1RouteARationalSignedJetRect3310

namespace ConnesWeilRH.Dev

theorem record2680_cell1_family_ne4_inactive3432
    (family : Fin 30) (hfamily : family ≠ 4) :
    ¬ |record2680CenterRat3279 1| < storedWidthRat3287 family ^ 2 := by
  fin_cases family <;>
    norm_num [record2680CenterRat3279, storedWidthRat3287,
      Matrix.cons_val_four] at hfamily ⊢ <;> simp_all

theorem ratBumpJetInterval3310_cell1_family_ne4_zero3432
    (order : ℕ) (family : Fin 30) (horder : order ≤ 2)
    (hfamily : family ≠ 4) :
    ratBumpJetInterval3310 order (storedWidthRat3287 family ^ 2)
      (record2680CenterRat3279 1) =
      ({lo := 0, hi := 0} : RatInterval3276) := by
  unfold ratBumpJetInterval3310
  rw [if_neg (record2680_cell1_family_ne4_inactive3432 family hfamily)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedUnitJetRect3310_cell1_family_ne4_zero3432
    (index : ℕ) (family : Fin 30) (hindex : index ≤ 2)
    (hfamily : family ≠ 4) :
    ratWeightedUnitJetRect3310 2 index 1 family =
      ({reLo := 0, reHi := 0, imLo := 0, imHi := 0} : RatRect3276) := by
  have hactive : ¬ |record2680CenterRat3279 1| <
      storedWidthRat3287 family ^ 2 :=
    record2680_cell1_family_ne4_inactive3432 family hfamily
  unfold ratWeightedUnitJetRect3310 ratBumpRect3310 ratBumpJetInterval3310
  rw [if_neg hactive]
  rw [ratRect_mul_zero_real3288]

theorem ratWeightedPhysicalTermRect3310_cell1_family_ne4_zero3432
    (family : Fin 30) (hfamily : family ≠ 4) :
    ratWeightedPhysicalTermRect3310 2 1 family =
      ({reLo := 0, reHi := 0, imLo := 0, imHi := 0} : RatRect3276) := by
  unfold ratWeightedPhysicalTermRect3310 ratWeightedUnitJetSumRect3310
  simp only [RatRect3276.sumFinset, Finset.sum_range_succ]
  rw [ratWeightedUnitJetRect3310_cell1_family_ne4_zero3432
    0 family (by norm_num) hfamily]
  rw [ratWeightedUnitJetRect3310_cell1_family_ne4_zero3432
    1 family (by norm_num) hfamily]
  rw [ratWeightedUnitJetRect3310_cell1_family_ne4_zero3432
    2 family (by norm_num) hfamily]
  norm_num [RatRect3276.sumFinset, Finset.sum_range_succ,
    RatRect3276.mul, RatInterval3276.mul, RatInterval3276.sub,
    RatInterval3276.add]

theorem ratWeightedPhysicalRect3310_cell1_eq_family4_3432 :
    ratWeightedPhysicalRect3310 2 1 =
      ratWeightedPhysicalTermRect3310 2 1 4 := by
  have hsum_zero (g : Fin 30 → ℚ)
      (hg : ∀ family : Fin 30, family ≠ 4 → g family = 0) :
      ∑ family : Fin 30, g family = g 4 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 4)]
    have hzero : ∑ family ∈ (Finset.univ : Finset (Fin 30)).erase 4,
        g family = 0 := by
      apply Finset.sum_eq_zero
      intro family hmem
      exact hg family (Finset.mem_erase.mp hmem).1
    rw [hzero, zero_add]
  have hrect_eq (a b : RatRect3276)
      (hreLo : a.reLo = b.reLo) (hreHi : a.reHi = b.reHi)
      (himLo : a.imLo = b.imLo) (himHi : a.imHi = b.imHi) : a = b := by
    cases a
    cases b
    simp_all
  have hreLo :
      (ratWeightedPhysicalRect3310 2 1).reLo =
        (ratWeightedPhysicalTermRect3310 2 1 4).reLo := by
    simp only [ratWeightedPhysicalRect3310, RatRect3276.sumFinset]
    simpa using hsum_zero
      (fun family =>
        (ratWeightedPhysicalTermRect3310 2 1 family).reLo)
      (fun family hfamily => by
        change (ratWeightedPhysicalTermRect3310 2 1 family).reLo = 0
        rw [ratWeightedPhysicalTermRect3310_cell1_family_ne4_zero3432
          family hfamily])
  have hreHi :
      (ratWeightedPhysicalRect3310 2 1).reHi =
        (ratWeightedPhysicalTermRect3310 2 1 4).reHi := by
    simp only [ratWeightedPhysicalRect3310, RatRect3276.sumFinset]
    simpa using hsum_zero
      (fun family =>
        (ratWeightedPhysicalTermRect3310 2 1 family).reHi)
      (fun family hfamily => by
        change (ratWeightedPhysicalTermRect3310 2 1 family).reHi = 0
        rw [ratWeightedPhysicalTermRect3310_cell1_family_ne4_zero3432
          family hfamily])
  have himLo :
      (ratWeightedPhysicalRect3310 2 1).imLo =
        (ratWeightedPhysicalTermRect3310 2 1 4).imLo := by
    simp only [ratWeightedPhysicalRect3310, RatRect3276.sumFinset]
    simpa using hsum_zero
      (fun family =>
        (ratWeightedPhysicalTermRect3310 2 1 family).imLo)
      (fun family hfamily => by
        change (ratWeightedPhysicalTermRect3310 2 1 family).imLo = 0
        rw [ratWeightedPhysicalTermRect3310_cell1_family_ne4_zero3432
          family hfamily])
  have himHi :
      (ratWeightedPhysicalRect3310 2 1).imHi =
        (ratWeightedPhysicalTermRect3310 2 1 4).imHi := by
    simp only [ratWeightedPhysicalRect3310, RatRect3276.sumFinset]
    simpa using hsum_zero
      (fun family =>
        (ratWeightedPhysicalTermRect3310 2 1 family).imHi)
      (fun family hfamily => by
        change (ratWeightedPhysicalTermRect3310 2 1 family).imHi = 0
        rw [ratWeightedPhysicalTermRect3310_cell1_family_ne4_zero3432
          family hfamily])
  exact hrect_eq _ _ hreLo hreHi himLo himHi

end ConnesWeilRH.Dev
