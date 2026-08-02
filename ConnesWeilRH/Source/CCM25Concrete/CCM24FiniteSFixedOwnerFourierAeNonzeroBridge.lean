/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedCompactRootFourierAeNonzeroBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryInjectivityGuard

/-!
# Selected-owner Fourier almost-everywhere nonvanishing bridge

Proof 703 supplies root nondegeneracy from a surviving arithmetic atom.
Proof 707 converts that root nondegeneracy, together with an explicit
analyticity premise for the Fourier transform, into the almost-everywhere
multiplier premise consumed by the full-boundary chain.  This module keeps
those two producers separate and only packages their owner-level composition.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedOwnerFourierAeNonzeroBridge

open MeasureTheory
open scoped FourierTransform

open CC20Concrete
open CCM24FiniteSFixedCompactRootFourierAeNonzeroBridge
open CCM24FiniteSFixedFullBoundaryInjectivityGuard

theorem sourceTest_fourier_ae_ne_zero_of_analytic_of_finitePrimeTerm_ne_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) {n : ℕ}
    (hterm : owner.finitePrimeTerm n ≠ 0)
    (hanalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ) :
    ∀ᵐ xi ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) xi ≠ 0 := by
  apply fourier_test_ae_ne_zero_of_analytic_of_test_ne_zero owner.sourceTest
    hanalytic
  exact sourceTest_ne_zero_of_finitePrimeTerm_ne_zero owner hterm

theorem sourceTest_fourier_ae_ne_zero_of_analytic_of_selectedVisiblePrime
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {p : CCM24VisiblePrime}
    (hp : p ∈
      CCM24FiniteSProjectionTrace.FinitePrimePowerFamily.visiblePrimes
        (CCM24FiniteSProjectionTrace.FinitePrimePowerFamily.ofSelectedOwner
          owner))
    (hanalytic :
      AnalyticOnNhd ℝ
        (fun xi : ℝ => FourierTransform.fourier owner.sourceTest.test xi)
        Set.univ) :
    ∀ᵐ xi ∂(volume : Measure ℝ),
      ((FourierTransform.fourier owner.sourceTest.test).toLp ⊤ : ℝ → ℂ) xi ≠ 0 := by
  apply fourier_test_ae_ne_zero_of_analytic_of_test_ne_zero owner.sourceTest
    hanalytic
  exact sourceTest_ne_zero_of_selectedVisiblePrime owner hp

end CCM24FiniteSFixedOwnerFourierAeNonzeroBridge
end CCM25Concrete
end Source
end ConnesWeilRH
