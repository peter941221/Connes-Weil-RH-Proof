import ConnesWeilRH.Dev.C1RouteBFiniteTargetAssembly2812
import ConnesWeilRH.Dev.C1RouteBSeedLedgerAllowanceContract3031

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
open Set
open scoped Interval

/-! The finite-target consumer with an explicit per-cell allowance.

The evaluator soundness theorem is intentionally a premise: this brick only
shows how a proved pointwise allowance is consumed by the existing partition
integral assembly.
-/
theorem routeB_finite_target_with_allowance3032
    {n : ℕ} {endpoint : ℕ → ℝ}
    (f4 f7 : ℝ → ℂ) (rect4 rect7 : ℕ → ComplexRect2427)
    (norm4 norm7 charge4 charge7 : ℕ → ℝ)
    {aggregate4 aggregate7 margin4 margin7 target4 target7 : ℝ}
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
    (hcont4 : Continuous f4) (hcont7 : Continuous f7)
    (hsum4 : (∑ k ∈ Finset.range n, charge4 k) ≤ aggregate4 + margin4)
    (hsum7 : (∑ k ∈ Finset.range n, charge7 k) ≤ aggregate7 + margin7)
    (htarget4 : aggregate4 + margin4 < target4)
    (htarget7 : aggregate7 + margin7 < target7) :
    (∫ x in (endpoint 0)..(endpoint n), ‖f4 x‖) < target4 ∧
    (∫ x in (endpoint 0)..(endpoint n), ‖f7 x‖) < target7 := by
  have hfin := routeB_finite_complex_d4d7_assembly2807 f4 f7 rect4 rect7
    norm4 norm7 charge4 charge7 hendpoint hrect4 hrect7 hnorm4 hnorm7
    hcharge4 hcharge7 hcont4 hcont7
  exact ⟨lt_of_le_of_lt (hfin.1.trans hsum4) htarget4,
    lt_of_le_of_lt (hfin.2.trans hsum7) htarget7⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
