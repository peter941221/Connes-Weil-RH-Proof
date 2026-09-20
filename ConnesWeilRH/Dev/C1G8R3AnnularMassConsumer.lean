/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3AnnularKernelDiagonalMass
import ConnesWeilRH.Dev.C1G8R3AnnularTailCosineRule

/-!
# Two-wing annular majorant consumer

This leaf reconnects the abstract two-sided cosine-rule assembly to the
source-root annular square-sum consumer.  It is an exact same-owner bridge:
an explicit nonnegative majorant for the kernel diagonal on the two outer
wings yields the uniform annular bound, and hence the source-compressed
root square-sum.  No majorant is constructed here and no sign is claimed.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedWeilSquare

theorem sourceCompressedRoot_squareSum_of_annular_wing_majorant
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    {g : ℝ → ℝ} {B₁ B₂ : ℝ}
    (hg : Measurable g) (hgnonneg : ∀ t, 0 ≤ g t)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hNpos : 0 < (N : ℝ))
    (hzero : ∀ t, -(N : ℝ) ≤ t → t ≤ (N : ℝ) → g t = 0)
    (hpoint : ∀ n, N ≤ n → ∀ t, ∑' i, ENNReal.ofReal
        (‖(sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t‖) ^ (2 : ℕ) ≤
        ENNReal.ofReal (g t))
    (hleft : ∫⁻ t in Set.Iic (-(N : ℝ)), ENNReal.ofReal (g t) ≤
      ENNReal.ofReal B₁)
    (hright : ∫⁻ t in Set.Ici (N : ℝ), ENNReal.ofReal (g t) ≤
      ENNReal.ofReal B₂) :
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  have hdiag : ∀ n, N ≤ n →
      ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (B₁ + B₂) := by
    intro n hn
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpoint_n : ∀ t, ∑' i, ENNReal.ofReal
        (‖(sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t‖) ^ (2 : ℕ) ≤
        ENNReal.ofReal (g t) := by
      intro t
      -- The cosine-rule majorant is independent of the outer cutoff.
      exact hpoint n hn t
    have hbound := annular_lintegral_le_of_pointwise
      (cols := fun i t =>
        (sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t)
      (g := g) (N := (N : ℝ)) (B₁ := B₁) (B₂ := B₂)
      hg hgnonneg hB₁ hB₂ hNpos hzero hpoint_n hleft hright
    simpa using hbound
  exact sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound
    owner lambda sourceBasis N hN (B := B₁ + B₂)
      (add_nonneg hB₁ hB₂) hdiag

end Dev
end ConnesWeilRH
