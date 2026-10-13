import ConnesWeilRH.Dev.C1RouteACellIntegralCharge2675

namespace ConnesWeilRH.Dev

open Set
open scoped Interval

/-- Cellwise rectangle and price certificates compose over a finite partition.
The theorem keeps every analytic obligation explicit while reducing the
global integral to the sum of local charges. -/
theorem weightedNormIntegral_le_of_partition2684
    {n : ℕ} {endpoint : ℕ → ℝ} {sigma : ℝ} {f : ℝ → ℂ}
    (rect : ℕ → ComplexRect2427)
    (weightBound normBound charge : ℕ → ℝ)
    (hendpoint : ∀ k, k < n → endpoint k ≤ endpoint (k + 1))
    (hrect : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      (rect k).Mem (f x))
    (hnorm : ∀ k, k < n → (rect k).cornerNorm ≤ normBound k)
    (hweight_nonneg : ∀ k, k < n → 0 ≤ weightBound k)
    (hweight : ∀ k, k < n → ∀ x ∈ Icc (endpoint k) (endpoint (k + 1)),
      Real.exp (sigma * x) ≤ weightBound k)
    (hintegrable : ∀ k, k < n → IntervalIntegrable
      (fun x => Real.exp (sigma * x) * ‖f x‖)
      MeasureTheory.volume (endpoint k) (endpoint (k + 1)))
    (hprice : ∀ k, k < n →
      (endpoint (k + 1) - endpoint k) *
        (weightBound k * normBound k) ≤ charge k) :
    (∫ x in (endpoint 0)..(endpoint n),
      Real.exp (sigma * x) * ‖f x‖) ≤
      ∑ k ∈ Finset.range n, charge k := by
  have hlocal : ∀ k, k < n →
      (∫ x in (endpoint k)..(endpoint (k + 1)),
        Real.exp (sigma * x) * ‖f x‖) ≤ charge k := by
    intro k hk
    have hcell := weightedNormIntegral_le_of_cellRectangle
      (a := endpoint k) (b := endpoint (k + 1)) (sigma := sigma)
      (weightBound := weightBound k) (normBound := normBound k)
      (rect := rect k) (hendpoint k hk) (hrect k hk)
      (hnorm k hk) (hweight_nonneg k hk) (hweight k hk)
      (hintegrable k hk)
    exact hcell.trans (hprice k hk)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => Real.exp (sigma * x) * ‖f x‖)
    (μ := MeasureTheory.volume) (a := endpoint) (n := n)
    (fun k hk => hintegrable k hk)
  calc
    (∫ x in (endpoint 0)..(endpoint n),
        Real.exp (sigma * x) * ‖f x‖) =
        ∑ k ∈ Finset.range n,
          ∫ x in (endpoint k)..(endpoint (k + 1)),
            Real.exp (sigma * x) * ‖f x‖ := hsum.symm
    _ ≤ ∑ k ∈ Finset.range n, charge k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hlocal k (Finset.mem_range.mp hk)

end ConnesWeilRH.Dev
