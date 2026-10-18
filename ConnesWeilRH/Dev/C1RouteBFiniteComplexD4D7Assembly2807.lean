import ConnesWeilRH.Dev.C1RouteAWeightedCellPartition2684

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
open Set
open scoped Interval

theorem routeB_finite_complex_d4d7_assembly2807
    {n : ℕ} {endpoint : ℕ → ℝ}
    (f4 f7 : ℝ → ℂ) (rect4 rect7 : ℕ → ComplexRect2427)
    (norm4 norm7 charge4 charge7 : ℕ → ℝ)
    (hendpoint : ∀ k, k < n → endpoint k ≤ endpoint (k + 1))
    (hrect4 : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (rect4 k).Mem (f4 x))
    (hrect7 : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (rect7 k).Mem (f7 x))
    (hnorm4 : ∀ k, k < n → (rect4 k).cornerNorm ≤ norm4 k)
    (hnorm7 : ∀ k, k < n → (rect7 k).cornerNorm ≤ norm7 k)
    (hcharge4 : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) * norm4 k ≤ charge4 k)
    (hcharge7 : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) * norm7 k ≤ charge7 k)
    (hcont4 : Continuous f4) (hcont7 : Continuous f7) :
    (∫ x in (endpoint 0)..(endpoint n), ‖f4 x‖) ≤
        ∑ k ∈ Finset.range n, charge4 k ∧
    (∫ x in (endpoint 0)..(endpoint n), ‖f7 x‖) ≤
        ∑ k ∈ Finset.range n, charge7 k := by
  have hi4 : ∀ k, k < n → IntervalIntegrable (fun x => ‖f4 x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)) := by
    intro k hk
    exact hcont4.norm.intervalIntegrable _ _
  have hi7 : ∀ k, k < n → IntervalIntegrable (fun x => ‖f7 x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)) := by
    intro k hk
    exact hcont7.norm.intervalIntegrable _ _
  have h4 := weightedNormIntegral_le_of_partition2684
    (sigma := 0) (f := f4) rect4 (fun _ => 1) norm4 charge4
    hendpoint hrect4 hnorm4 (fun _ _ => by norm_num)
    (fun _ _ _ _ => by simp) (fun k hk => by simpa using hi4 k hk)
    (fun k hk => by simpa using hcharge4 k hk)
  have h7 := weightedNormIntegral_le_of_partition2684
    (sigma := 0) (f := f7) rect7 (fun _ => 1) norm7 charge7
    hendpoint hrect7 hnorm7 (fun _ _ => by norm_num)
    (fun _ _ _ _ => by simp) (fun k hk => by simpa using hi7 k hk)
    (fun k hk => by simpa using hcharge7 k hk)
  exact ⟨by simpa using h4, by simpa using h7⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
