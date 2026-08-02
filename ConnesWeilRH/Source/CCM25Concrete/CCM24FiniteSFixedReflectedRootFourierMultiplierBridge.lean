/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge

/-!
# Reflected-root Fourier multiplier bridge

The full-boundary injectivity consumer uses the involuted compact root
`g.involution.test`.  This module records the exact Fourier identity relating
that multiplier to the original compact root.  It transfers an
almost-everywhere nonvanishing hypothesis without claiming the missing
Paley--Wiener zero-set theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedReflectedRootFourierMultiplierBridge

open MeasureTheory
open scoped FourierTransform

open CompactLogConvolution

theorem fourier_involution_test_apply
    (g : CompactLogTest) (xi : ℝ) :
    (FourierTransform.fourier g.involution.test) xi =
      star ((FourierTransform.fourier g.test) xi) := by
  exact SelectedCrossingOperatorBridge.fourier_compactLogTest_involution g xi

theorem fourier_involution_test_ae_ne_zero_of_fourier_test_ae_ne_zero
    (g : CompactLogTest)
    (hfourier : ∀ᵐ xi ∂(volume : Measure ℝ),
      ((FourierTransform.fourier g.test).toLp ⊤ : ℝ → ℂ) xi ≠ 0) :
    ∀ᵐ xi ∂(volume : Measure ℝ),
      ((FourierTransform.fourier g.involution.test).toLp ⊤ : ℝ → ℂ) xi ≠ 0 := by
  filter_upwards [hfourier,
    SchwartzMap.coeFn_toLp (FourierTransform.fourier g.test) ⊤,
    SchwartzMap.coeFn_toLp (FourierTransform.fourier g.involution.test) ⊤]
      with xi htest htestLp hinvolutionLp
  rw [hinvolutionLp, fourier_involution_test_apply, ← htestLp]
  exact star_ne_zero.mpr htest

end CCM24FiniteSFixedReflectedRootFourierMultiplierBridge
end CCM25Concrete
end Source
end ConnesWeilRH
