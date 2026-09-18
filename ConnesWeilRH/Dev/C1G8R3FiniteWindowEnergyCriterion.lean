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

/-
A fixed finite window is already a square-summable operator.  Consequently,
the only genuinely new estimate needed for an expanding family is a uniform
finite-set estimate for its annular difference from that fixed window.  This
lemma records the quantitative two-term estimate used below.
-/
theorem eventual_uniform_finite_window_energy_of_fixed_plus_tail
    {ι H G : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (basis : HilbertBasis ι ℂ H)
    (head : H →L[ℂ] G) (tail : ℕ → H →L[ℂ] G)
    (hhead : Summable fun i => ‖head (basis i)‖ ^ 2)
    {C : ℝ} (N : ℕ)
    (htail : ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖tail n (basis i)‖ ^ 2 ≤ C) :
    ∀ n, N ≤ n → ∀ s : Finset ι,
      ∑ i ∈ s, ‖(head + tail n) (basis i)‖ ^ 2 ≤
        2 * ((∑' i, ‖head (basis i)‖ ^ 2) + C) := by
  intro n hn s
  have hhead_sum : ∑ i ∈ s, ‖head (basis i)‖ ^ 2 ≤
      ∑' i, ‖head (basis i)‖ ^ 2 :=
    hhead.sum_le_tsum s (fun i _ => sq_nonneg _)
  have htail_sum := htail n hn s
  have hterm (i : ι) :
      ‖(head + tail n) (basis i)‖ ^ 2 ≤
        2 * ‖head (basis i)‖ ^ 2 + 2 * ‖tail n (basis i)‖ ^ 2 := by
    simp only [ContinuousLinearMap.add_apply]
    calc
      ‖head (basis i) + tail n (basis i)‖ ^ 2 ≤
          (‖head (basis i)‖ + ‖tail n (basis i)‖) ^ 2 := by
            exact (sq_le_sq₀ (norm_nonneg _)
              (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
              (norm_add_le _ _)
      _ ≤ 2 * ‖head (basis i)‖ ^ 2 +
          2 * ‖tail n (basis i)‖ ^ 2 := by
            nlinarith [sq_nonneg
              (‖head (basis i)‖ - ‖tail n (basis i)‖)]
  calc
    ∑ i ∈ s, ‖(head + tail n) (basis i)‖ ^ 2 ≤
        ∑ i ∈ s, (2 * ‖head (basis i)‖ ^ 2 +
          2 * ‖tail n (basis i)‖ ^ 2) := by
            exact Finset.sum_le_sum fun i hi => hterm i
    _ = 2 * (∑ i ∈ s, ‖head (basis i)‖ ^ 2) +
        2 * (∑ i ∈ s, ‖tail n (basis i)‖ ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (∑' i, ‖head (basis i)‖ ^ 2) + 2 * C := by
      gcongr
    _ = 2 * ((∑' i, ‖head (basis i)‖ ^ 2) + C) := by ring

end Dev
end ConnesWeilRH
