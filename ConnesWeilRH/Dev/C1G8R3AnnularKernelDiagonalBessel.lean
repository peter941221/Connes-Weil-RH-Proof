/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3AnnularTailCosineRule

/-!
# Bessel-to-diagonal bridge for the annular producer

This leaf isolates the exact pointwise analytic input needed by the annular
mass consumer.  If the output columns are pairings against a kernel vector,
and the carrier projection of that vector is bounded by a real majorant, then
Bessel's identity gives the required ENNReal kernel-diagonal bound.  No
convolution readback or density extension is assumed here.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory RCLike

theorem annular_kernelDiagonal_le_of_inner_kernel_projection_majorant
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ K)
    {cols : ι → ℝ → ℂ} {kernel : ℝ → H} {g : ℝ → ℝ}
    (hcols : ∀ i t,
      cols i t = inner ℂ ((basis i : K) : H) (kernel t))
    (hmajor : ∀ t,
      ‖K.starProjection (kernel t)‖ ^ 2 ≤ g t) :
    ∀ t, ∑' i, ENNReal.ofReal (‖cols i t‖) ^ (2 : ℕ) ≤
      ENNReal.ofReal (g t) := by
  intro t
  have hsum : ∑' i, ‖cols i t‖ ^ (2 : ℕ) =
      ‖K.starProjection (kernel t)‖ ^ (2 : ℕ) := by
    calc
      ∑' i, ‖cols i t‖ ^ (2 : ℕ) =
          ∑' i, ‖inner ℂ ((basis i : K) : H) (kernel t)‖ ^ (2 : ℕ) := by
            apply tsum_congr
            intro i
            rw [hcols]
      _ = re (inner ℂ (K.starProjection (kernel t))
          (K.starProjection (kernel t))) :=
        tsum_norm_inner_sq_eq_starProjection_normSq K basis (kernel t)
      _ = ‖K.starProjection (kernel t)‖ ^ (2 : ℕ) := by
        exact inner_self_eq_norm_sq _
  have hpair : ∀ i,
      inner ℂ ((basis i : K) : H) (K.starProjection (kernel t)) =
        inner ℂ ((basis i : K) : H) (kernel t) := by
    intro i
    have h0 := K.starProjection_inner_eq_zero (kernel t)
      (basis i : H) (Submodule.coe_mem (basis i))
    have h1 : inner ℂ ((basis i : K) : H)
        (kernel t - K.starProjection (kernel t)) = 0 := by
      rw [← inner_conj_symm, h0]
      simp
    rw [inner_sub_right, sub_eq_zero] at h1
    exact h1.symm
  have hs : Summable (fun i => ‖cols i t‖ ^ (2 : ℕ)) := by
    let p : K := K.orthogonalProjection (kernel t)
    have hs0 : Summable (fun i : ι =>
        inner ℂ p (basis i) * inner ℂ (basis i) p) :=
      basis.summable_inner_mul_inner p p
    have hs1 : Summable (fun i =>
        ‖inner ℂ ((basis i : K) : H) (K.starProjection (kernel t))‖ ^
          (2 : ℕ)) := by
      have heq : (fun i : ι =>
          ‖inner ℂ ((basis i : K) : H) (K.starProjection (kernel t))‖ ^
            (2 : ℕ)) =
          (fun i : ι =>
            ‖inner ℂ p (basis i) * inner ℂ (basis i) p‖) := by
        funext i
        change ‖inner ℂ ((basis i : K) : H) (K.starProjection (kernel t))‖ ^
            (2 : ℕ) =
          ‖inner ℂ p (basis i) * inner ℂ (basis i) p‖
        simp only [Submodule.coe_inner]
        rw [norm_mul]
        change ‖inner ℂ ((basis i : K) : H) (p : H)‖ ^ (2 : ℕ) =
          ‖inner ℂ (p : H) (basis i : H)‖ *
            ‖inner ℂ (basis i : H) (p : H)‖
        rw [← inner_conj_symm]
        rw [norm_conj]
        ring
      rw [heq]
      exact hs0.norm
    have heq : (fun i : ι => ‖cols i t‖ ^ (2 : ℕ)) =
        (fun i : ι =>
          ‖inner ℂ ((basis i : K) : H) (K.starProjection (kernel t))‖ ^
            (2 : ℕ)) := by
      funext i
      rw [hcols, hpair]
    rw [heq]
    exact hs1
  calc
    ∑' i, ENNReal.ofReal (‖cols i t‖) ^ (2 : ℕ) =
        ∑' i, ENNReal.ofReal (‖cols i t‖ ^ (2 : ℕ)) := by
          apply tsum_congr
          intro i
          rw [ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∑' i, ‖cols i t‖ ^ (2 : ℕ)) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun i => sq_nonneg (‖cols i t‖))
        hs).symm
    _ = ENNReal.ofReal (‖K.starProjection (kernel t)‖ ^ (2 : ℕ)) := by
      rw [hsum]
    _ ≤ ENNReal.ofReal (g t) :=
      ENNReal.ofReal_le_ofReal (hmajor t)

end Dev
end ConnesWeilRH
