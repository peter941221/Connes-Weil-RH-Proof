/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedCompactRootFourierAeNonzeroBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedReflectedRootFourierMultiplierBridge

/-!
# Yoshida Mellin-zero versus `L2` root-kernel guard

The selected Yoshida construction prescribes isolated Mellin values of the
compact root.  The finite-S physical Gate instead uses its whole-line `L2`
convolution.  This file records the precise distinction: a nonzero normalized
Mellin value makes the root nonzero, and an analytic Fourier multiplier of a
nonzero compact root is nonzero almost everywhere.  Hence the global root
convolution has no nonzero `L2` kernel.

Consequently, an isolated off-critical Mellin zero cannot justify a step that
sets the root image of a nonzero Sonin vector to zero.  Any Gate 3U
cancellation must remain in the completed signed physical trace.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalYoshidaMellinZeroL2Guard

open MeasureTheory
open scoped FourierTransform

open CC20Concrete
open CC20YoshidaConvolution.CompactLogTest
open CCM24FiniteSBandTrace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFixedCompactRootFourierAeNonzeroBridge
open CCM24FiniteSFixedFullBoundaryWindowUniquenessBridge
open CCM24FiniteSFixedReflectedRootFourierMultiplierBridge
open UnscaledYoshidaSelectedOwner

/-- A nonzero Mellin value prevents the selected compact root from being the
zero Schwartz function. -/
theorem selectedOwner_sourceTest_ne_zero_of_laplaceAt_ne_zero
    (base correction : CompactLogConvolution.CompactLogTest) (n : Nat) (s : Complex)
    (hvalue : laplaceAt (selectedOwner base correction n).sourceTest s ≠ 0) :
    (selectedOwner base correction n).sourceTest.test ≠ 0 := by
  intro hzero
  apply hvalue
  unfold laplaceAt
  calc
    ∫ x : Real, (exponentialWeight (selectedOwner base correction n).sourceTest s).test x =
        ∫ _x : Real, (0 : Complex) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [exponentialWeight_apply]
      rw [DFunLike.congr_fun hzero x]
      simp
    _ = 0 := by simp

/-- The normalized source Mellin value in the unscaled Yoshida construction
is already enough to make the actual selected root nonzero. -/
theorem selectedOwner_sourceTest_ne_zero_of_centered_laplaceAt_eq_one
    (base correction : CompactLogConvolution.CompactLogTest) (n : Nat) (z : Complex)
    (hvalue :
      laplaceAt (selectedOwner base correction n).sourceTest (z - 1 / 2) = 1) :
    (selectedOwner base correction n).sourceTest.test ≠ 0 := by
  apply selectedOwner_sourceTest_ne_zero_of_laplaceAt_ne_zero base correction n
    (z - 1 / 2)
  rw [hvalue]
  norm_num

/-- Under the existing Fourier analyticity premise, the reflected selected
root has no nonzero global `L2` kernel. -/
theorem selectedOwner_rootConvolution_eq_zero_implies_eq_zero_of_fourier_ae_ne_zero
    (base correction : CompactLogConvolution.CompactLogTest) (n : Nat)
    (hmultiplier :
      ∀ᵐ xi : Real ∂(volume : Measure Real),
        ((FourierTransform.fourier (selectedOwner base correction n).sourceTest.test).toLp
          ⊤ : Real → Complex) xi ≠ 0)
    {u : finiteSCarrier}
    (hu : rootConvolution (selectedOwner base correction n) u = 0) :
    u = 0 := by
  apply cc20GlobalLogConvolution_injective_of_fourierMultiplier_ae_ne_zero
    (selectedOwner base correction n).sourceTest.involution.test
  · exact fourier_involution_test_ae_ne_zero_of_fourier_test_ae_ne_zero
      (selectedOwner base correction n).sourceTest hmultiplier
  · simpa only [rootConvolution] using hu

/-- A normalized Yoshida Mellin value and Fourier analyticity make the
selected root convolution injective on the actual global `L2` carrier. -/
theorem selectedOwner_rootConvolution_eq_zero_implies_eq_zero_of_centered_laplaceAt_eq_one
    (base correction : CompactLogConvolution.CompactLogTest) (n : Nat) (z : Complex)
    (hvalue :
      laplaceAt (selectedOwner base correction n).sourceTest (z - 1 / 2) = 1)
    (hanalytic :
      AnalyticOnNhd Real
        (fun xi : Real =>
          FourierTransform.fourier (selectedOwner base correction n).sourceTest.test xi)
        Set.univ)
    {u : finiteSCarrier}
    (hu : rootConvolution (selectedOwner base correction n) u = 0) :
    u = 0 := by
  apply selectedOwner_rootConvolution_eq_zero_implies_eq_zero_of_fourier_ae_ne_zero
    base correction n
  · exact fourier_test_ae_ne_zero_of_analytic_of_test_ne_zero
      (selectedOwner base correction n).sourceTest hanalytic
      (selectedOwner_sourceTest_ne_zero_of_centered_laplaceAt_eq_one
        base correction n z hvalue)
  · exact hu

/-- The raw Yoshida normalization transports to the centered selected root,
so it has the same `L2` injectivity consequence. -/
theorem selectedOwner_rootConvolution_eq_zero_implies_eq_zero_of_raw_laplaceAt_eq_one
    (base correction : CompactLogConvolution.CompactLogTest) (n : Nat) (z : Complex)
    (hvalue : laplaceAt ((convolutionIterate base n).convolution correction) z = 1)
    (hanalytic :
      AnalyticOnNhd Real
        (fun xi : Real =>
          FourierTransform.fourier (selectedOwner base correction n).sourceTest.test xi)
        Set.univ)
    {u : finiteSCarrier}
    (hu : rootConvolution (selectedOwner base correction n) u = 0) :
    u = 0 := by
  apply selectedOwner_rootConvolution_eq_zero_implies_eq_zero_of_centered_laplaceAt_eq_one
    base correction n z
  · rw [selectedOwner_laplaceAt_sourceTest_centered]
    exact hvalue
  · exact hanalytic
  · exact hu

end CCM24FiniteSGatePhysicalYoshidaMellinZeroL2Guard
end CCM25Concrete
end Source
end ConnesWeilRH
