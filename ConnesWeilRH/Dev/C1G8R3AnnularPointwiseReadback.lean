/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SourceRootFiniteWindowCriterion

/-!
# Pointwise readback of the source-root annulus

The source-root annular output is defined as the difference of two expanding
interval projections.  This leaf exposes its actual function-level shape:
the indicator of the outer symmetric interval minus the inner one, applied to
the same root-convolution output.  It is the exact starting point for a
kernel-diagonal or local-trace estimate; it asserts no bound and no RH sign.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CC20Concrete.CompactRootHalfLinePair
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare

theorem sourceRootAnnularOutputWindow_coeFn_eq_annulus_indicator
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) (hNn : N ≤ n) (u : sourceSoninCarrier lambda) :
    (sourceRootAnnularOutputWindow owner lambda N n u : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc (-(n : ℝ)) (n : ℝ) \ Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
        (fun t => (rootConvolution owner (sourceInclusion lambda u) : ℝ → ℂ) t) := by
  have hn := kernelIntervalProjection_coeFn
    (-(n : ℝ)) (n : ℝ) 0
    (rootConvolution owner (sourceInclusion lambda u))
  have hN := kernelIntervalProjection_coeFn
    (-(N : ℝ)) (N : ℝ) 0
    (rootConvolution owner (sourceInclusion lambda u))
  rw [sourceRootAnnularOutputWindow]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  have hsub := Lp.coeFn_sub
    (kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0
      (rootConvolution owner (sourceInclusion lambda u)))
    (kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0
      (rootConvolution owner (sourceInclusion lambda u)))
  filter_upwards [hsub, hn, hN] with t hsub hnt hNt
  have hnt' :
      (kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0
          (rootConvolution owner (sourceInclusion lambda u)) : ℝ → ℂ) t =
        (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator
          (fun s => (rootConvolution owner (sourceInclusion lambda u) : ℝ → ℂ) s) t := by
    simpa only [sub_zero, add_zero] using hnt
  have hNt' :
      (kernelIntervalProjection (-(N : ℝ)) (N : ℝ) 0
          (rootConvolution owner (sourceInclusion lambda u)) : ℝ → ℂ) t =
        (Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
          (fun s => (rootConvolution owner (sourceInclusion lambda u) : ℝ → ℂ) s) t := by
    simpa only [sub_zero, add_zero] using hNt
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hnt', hNt']
  have hcontain :
      Set.Icc (-(N : ℝ)) (N : ℝ) ⊆ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    intro x hx
    constructor
    · exact neg_le_neg (by exact_mod_cast hNn) |>.trans hx.1
    · exact hx.2.trans (by exact_mod_cast hNn)
  by_cases hout : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  · by_cases hin : t ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
    · have hdiff : t ∉ Set.Icc (-(n : ℝ)) (n : ℝ)
          \ Set.Icc (-(N : ℝ)) (N : ℝ) := by
        exact fun ht => ht.2 hin
      simp only [Set.indicator_of_mem hout, Set.indicator_of_mem hin,
        Set.indicator_of_notMem hdiff]
      simp
    · have hdiff : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
          \ Set.Icc (-(N : ℝ)) (N : ℝ) := ⟨hout, hin⟩
      simp only [Set.indicator_of_mem hout, Set.indicator_of_notMem hin,
        Set.indicator_of_mem hdiff]
      simp
  · have hin : t ∉ Set.Icc (-(N : ℝ)) (N : ℝ) := by
      intro ht
      exact hout (hcontain ht)
    have hdiff : t ∉ Set.Icc (-(n : ℝ)) (n : ℝ)
          \ Set.Icc (-(N : ℝ)) (N : ℝ) := by
      exact fun ht => hout ht.1
    simp only [Set.indicator_of_notMem hout, Set.indicator_of_notMem hin,
      Set.indicator_of_notMem hdiff]
    simp

end Dev
end ConnesWeilRH
