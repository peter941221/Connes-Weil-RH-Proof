/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3AnnularKernelDiagonalTonelli
import ConnesWeilRH.Dev.C1CC20KernelLpLift

/-!
# Exact annular kernel-diagonal mass identity

This is the operator-level interface for the live S3 producer.  It combines
the L2 annular readback with Tonelli, without inserting a finite-dimensional
or basis-smoothness assumption.  The remaining analytic input is therefore a
uniform bound on the right-hand diagonal integral.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedWeilSquare
open Source.C1CC20KernelLpLift

theorem sourceRootAnnularOutputWindow_normSq_tsum_eq_kernelDiagonal_lintegral
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    (hn : selectedRootSupportRadius owner ≤ (n : ℝ))
    (hNn : N ≤ n) {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ENNReal.ofReal (∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
      (sourceBasis i)‖ ^ 2) =
      ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) := by
  have hs : Summable (fun i =>
    ‖sourceRootAnnularOutputWindow owner lambda N n
      (sourceBasis i)‖ ^ 2) :=
    sourceRootAnnularOutputWindow_sourceBasis_normSq_summable
      owner lambda N n hN hn sourceBasis
  calc
    ENNReal.ofReal (∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2) =
        ∑' i, ENNReal.ofReal
          (‖sourceRootAnnularOutputWindow owner lambda N n
            (sourceBasis i)‖ ^ 2) := by
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun i => sq_nonneg _) hs
    _ = ∑' i, ∫⁻ t, ‖(sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) := by
      apply tsum_congr
      intro i
      have hmem := Lp.memLp
        (sourceRootAnnularOutputWindow owner lambda N n (sourceBasis i))
      have hint : Integrable (fun t : ℝ =>
          ‖(sourceRootAnnularOutputWindow owner lambda N n
            (sourceBasis i) : ℝ → ℂ) t‖ ^ 2) :=
        (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
      calc
        ENNReal.ofReal
            (‖sourceRootAnnularOutputWindow owner lambda N n
              (sourceBasis i)‖ ^ 2) =
            ENNReal.ofReal (∫ t, ‖(sourceRootAnnularOutputWindow
              owner lambda N n (sourceBasis i) : ℝ → ℂ) t‖ ^ 2) := by
          have hto := Lp.toLp_coeFn
            (sourceRootAnnularOutputWindow owner lambda N n (sourceBasis i))
            hmem
          calc
            ENNReal.ofReal
                (‖sourceRootAnnularOutputWindow owner lambda N n
                  (sourceBasis i)‖ ^ 2) =
                ENNReal.ofReal
                  (‖hmem.toLp
                    (sourceRootAnnularOutputWindow owner lambda N n
                      (sourceBasis i) : ℝ → ℂ)‖ ^ 2) := by rw [hto]
            _ = ENNReal.ofReal (∫ t, ‖(sourceRootAnnularOutputWindow
                  owner lambda N n (sourceBasis i) : ℝ → ℂ) t‖ ^ 2) := by
              rw [norm_toLp_sq_eq_integral_norm_sq hmem]
        _ = ∫⁻ t, ‖(sourceRootAnnularOutputWindow owner lambda N n
              (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) := by
          simpa only [Real.rpow_two] using
            (bochner_sq_norm_eq_lintegral_enorm_sq_general hint)
    _ = ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) := by
      symm
      exact sourceRootAnnularOutputWindow_lintegral_tsum_eq_tsum_lintegral
        owner lambda N n sourceBasis

theorem sourceCompressedRoot_squareSum_of_kernelDiagonal_lintegral_bound
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (N : ℕ) (hN : selectedRootSupportRadius owner ≤ (N : ℝ))
    {B : ℝ} (hB : 0 ≤ B)
    (hdiag : ∀ n, N ≤ n →
      ∫⁻ t, ∑' i, ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal B) :
    Summable fun i => ‖sourceCompressedRoot owner lambda
      (sourceBasis i)‖ ^ 2 := by
  apply sourceCompressedRoot_squareSum_of_eventual_annular_tsum_energy
    (B := B) owner lambda sourceBasis N hN
  intro n hn
  have hn' : selectedRootSupportRadius owner ≤ (n : ℝ) :=
    le_trans hN (by exact_mod_cast hn)
  have hmass :=
    sourceRootAnnularOutputWindow_normSq_tsum_eq_kernelDiagonal_lintegral
      owner lambda N n hN hn' hn sourceBasis
  have hle : ENNReal.ofReal
      (∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2) ≤ ENNReal.ofReal B := by
    rw [hmass]
    exact hdiag n hn
  have hroot : (∑' i, ‖sourceRootAnnularOutputWindow owner lambda N n
      (sourceBasis i)‖ ^ 2) ≤ B :=
    (ENNReal.ofReal_le_ofReal_iff hB).mp hle
  have hscomp := sourceCompressedRootAnnularWindow_sourceBasis_normSq_summable
    owner lambda N n hN hn' sourceBasis
  have hsroot := sourceRootAnnularOutputWindow_sourceBasis_normSq_summable
    owner lambda N n hN hn' sourceBasis
  have hpoint : ∀ i, ‖sourceCompressedRootAnnularWindow owner lambda N n
      (sourceBasis i)‖ ^ 2 ≤ ‖sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i)‖ ^ 2 := by
    intro i
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (sourceCompressedRootAnnularWindow_norm_le_annularOutput_norm
        owner lambda N n (sourceBasis i))
  exact (hscomp.tsum_le_tsum hpoint hsroot).trans hroot

end Dev
end ConnesWeilRH
