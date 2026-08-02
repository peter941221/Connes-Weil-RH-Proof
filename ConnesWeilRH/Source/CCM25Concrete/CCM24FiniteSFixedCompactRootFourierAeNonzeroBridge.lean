/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryOriginalRootMultiplierBridge
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology

/-!
# Compact-root Fourier almost-everywhere nonvanishing bridge

An analytic Fourier transform which is not identically zero has only a
locally discrete real zero set.  This module converts that exact analytic
premise, together with a nonzero compact root, into the `Lp` almost-everywhere
multiplier premise consumed by the full-boundary chain.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedCompactRootFourierAeNonzeroBridge

open MeasureTheory
open scoped FourierTransform

theorem fourier_test_ae_ne_zero_of_analytic_of_test_ne_zero
    (g : CompactLogConvolution.CompactLogTest)
    (hanalytic :
      AnalyticOnNhd ℝ (fun xi : ℝ => (FourierTransform.fourier g.test) xi)
        Set.univ)
    (hroot : g.test ≠ 0) :
    ∀ᵐ xi ∂(volume : Measure ℝ),
      ((FourierTransform.fourier g.test).toLp ⊤ : ℝ → ℂ) xi ≠ 0 := by
  have hfourier : FourierTransform.fourier g.test ≠ 0 := by
    intro hzero
    apply hroot
    apply (FourierTransform.fourierCLE ℝ (SchwartzMap ℝ ℂ)).injective
    simpa using hzero
  have hvalue : ∃ xi : ℝ, (FourierTransform.fourier g.test) xi ≠ 0 := by
    by_contra hnone
    apply hfourier
    ext xi
    by_contra hxi
    exact hnone ⟨xi, hxi⟩
  rcases hvalue with ⟨xi, hxi⟩
  have hcodiscrete :=
    hanalytic.preimage_zero_mem_codiscrete (x := xi) hxi
  have hcodiscrete' :
      ∀ᶠ xi : ℝ in Filter.codiscrete ℝ,
        (FourierTransform.fourier g.test) xi ≠ 0 := by
    simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      ne_eq] using hcodiscrete
  have hae : ae (volume : Measure ℝ) ≤ Filter.codiscrete ℝ := by
    simpa only [Measure.restrict_univ] using
      (ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ))
        (U := Set.univ) MeasurableSet.univ)
  have hne : ∀ᵐ xi ∂(volume : Measure ℝ),
      (FourierTransform.fourier g.test) xi ≠ 0 :=
    hae hcodiscrete'
  filter_upwards [hne, SchwartzMap.coeFn_toLp
    (FourierTransform.fourier g.test) ⊤] with xi hxi hLp
  rw [hLp]
  exact hxi

end CCM24FiniteSFixedCompactRootFourierAeNonzeroBridge
end CCM25Concrete
end Source
end ConnesWeilRH
