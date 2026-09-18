/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3OutputProjectionStrongLimit

/-!
# Finite-window criterion for the survivor-core energy

This leaf isolates the exact reverse-limit principle needed by the direct
source-compressed route.  Strong convergence of expanding output windows is
not itself a trace argument; a uniform finite-window square-sum bound is the
missing hypothesis.  The theorem below makes that separation formal.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open scoped Topology

theorem summable_normSq_of_uniform_finite_window_energy
    {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (basis : HilbertBasis ι ℂ H) (T : H →L[ℂ] G)
    (approximant : ℕ → H →L[ℂ] G)
    (hstrong : ∀ x, Tendsto (fun n => approximant n x) atTop (𝓝 (T x)))
    {B : ℝ}
    (hbound : ∀ n (s : Finset ι),
      ∑ i ∈ s, ‖approximant n (basis i)‖ ^ 2 ≤ B) :
    Summable (fun i => ‖T (basis i)‖ ^ 2) := by
  apply summable_of_sum_le
  · intro i
    positivity
  · intro s
    have hsum : Tendsto
        (fun n => ∑ i ∈ s, ‖approximant n (basis i)‖ ^ 2)
        atTop (𝓝 (∑ i ∈ s, ‖T (basis i)‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro i hi
      exact ((continuous_norm.pow 2).tendsto (T (basis i))).comp
        (hstrong (basis i))
    exact le_of_tendsto hsum (Filter.Eventually.of_forall (fun n => hbound n s))

/-
The finite-window estimate is only needed on the eventual tail of the
expanding family.  This is the form consumed by source-compressed root
windows: the selected-root support theorem supplies a threshold, while the
finitely many smaller windows have no bearing on the reverse-limit argument.
-/
theorem summable_normSq_of_eventual_uniform_finite_window_energy
    {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (basis : HilbertBasis ι ℂ H) (T : H →L[ℂ] G)
    (approximant : ℕ → H →L[ℂ] G)
    (hstrong : ∀ x, Tendsto (fun n => approximant n x) atTop (𝓝 (T x)))
    {B : ℝ} (N : ℕ)
    (hbound : ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖approximant n (basis i)‖ ^ 2 ≤ B) :
    Summable (fun i => ‖T (basis i)‖ ^ 2) := by
  let tailApproximant : ℕ → H →L[ℂ] G := fun n => approximant (n + N)
  have htailStrong : ∀ x, Tendsto (fun n => tailApproximant n x)
      atTop (𝓝 (T x)) := by
    intro x
    simpa [tailApproximant, Nat.add_comm] using
      (hstrong x).comp (Filter.tendsto_add_atTop_nat N)
  apply summable_normSq_of_uniform_finite_window_energy basis T tailApproximant
    htailStrong
  intro n s
  exact hbound (n + N) (by omega) s

end Dev
end ConnesWeilRH
