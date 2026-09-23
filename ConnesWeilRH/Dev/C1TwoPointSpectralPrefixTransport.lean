/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1TwoPointSpectralDecomposition

/-!
# Two-point spectral-prefix transport on the selected detector owner

The two-point annihilator is now applied to the actual selected detector, not
only to the narrow auxiliary root.  Its Laplace multiplier preserves every
zero of the detector and therefore preserves every zero of the Hermitian
convolution square.  The annihilator-detector span consequently has no finite
prefix contribution away from the selected orbit, while its selected orbit
term is exactly a negative square.

This is a producer brick for the phase-balanced two-span spectral route.  It
does not assert a gate sign for the annihilated detector; that remains a
separate analytic obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1TwoPointSpectralPrefixTransport

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaDetector
open C1SameOwnerWeil
open C1TwoPointDifferentialAnnihilator
open C1TwoPointSpectralDecomposition
open C1SpectralWeil
open scoped BigOperators

noncomputable section

/-- A zero of the detector square is preserved by the annihilator-detector
    span, because the annihilator multiplies both Laplace factors by a scalar
    polynomial and the span retains the original detector as a factor. -/
theorem annihilatorDetectorSpanVector_convolutionSquare_laplaceAt_eq_zero_of_detectorSquare_eq_zero
    (g : CompactLogTest) (rho : ℂ) (lambda : Real) (s : ℂ)
    (hzero : laplaceAt g.convolutionSquare s = 0) :
    laplaceAt
        (annihilatorDetectorSpanVector (offlineZeroOrbitAnnihilator g rho) g lambda).convolutionSquare
        s = 0 := by
  have hfactor := laplaceAt_convolutionSquare g s
  rw [hzero] at hfactor
  rcases mul_eq_zero.mp hfactor.symm with hpartner | hvalue
  · have hpartner' :
        laplaceAt g (-star s) = 0 := by
      simpa using hpartner
    have hu :
        laplaceAt (offlineZeroOrbitAnnihilator g rho) (-star s) = 0 := by
      exact twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
        g (rho - 1 / 2) (1 - star rho - 1 / 2) (-star s) hpartner'
    have hv :
        laplaceAt
          (annihilatorDetectorSpanVector (offlineZeroOrbitAnnihilator g rho) g lambda)
          (-star s) = 0 := by
      rw [laplaceAt_annihilatorDetectorSpanVector, hu, hpartner']
      simp
    rw [laplaceAt_convolutionSquare, hv]
    simp
  · have hu :
        laplaceAt (offlineZeroOrbitAnnihilator g rho) s = 0 := by
      exact twoPointDerivativeAnnihilator_laplaceAt_eq_zero_of_laplaceAt_eq_zero
        g (rho - 1 / 2) (1 - star rho - 1 / 2) s hvalue
    have hv :
        laplaceAt
          (annihilatorDetectorSpanVector (offlineZeroOrbitAnnihilator g rho) g lambda)
          s = 0 := by
      rw [laplaceAt_annihilatorDetectorSpanVector, hu, hvalue]
      simp
    rw [laplaceAt_convolutionSquare, hv]
    simp

/-- At the selected off-line zero, the annihilator-detector span square has
    the exact negative target value `-lambda^2`. -/
theorem annihilatorDetectorSpanVector_convolutionSquare_laplaceAt_rho_sub_half_eq_neg_sq
    (g : CompactLogTest) (rho : ℂ) (lambda : Real)
    (hg1 : laplaceAt g (rho - 1 / 2) = 1)
    (hg2 : laplaceAt g (1 - star rho - 1 / 2) = -1) :
    laplaceAt
        (annihilatorDetectorSpanVector (offlineZeroOrbitAnnihilator g rho) g lambda).convolutionSquare
        (rho - 1 / 2) = -((lambda : ℂ) ^ 2) := by
  have hpair := pairedProduct_annihilatorDetectorSpanVector_eq_neg_sq
    (offlineZeroOrbitAnnihilator g rho) g lambda rho
    (offlineZeroOrbitAnnihilator_laplaceAt_rho_sub_half g rho)
    hg1
    (offlineZeroOrbitAnnihilator_laplaceAt_one_sub_star_rho_sub_half g rho)
    hg2
  have hcoord : -star (rho - 1 / 2) = 1 - star rho - 1 / 2 := by
    apply Complex.ext <;> simp [Complex.star_def] <;> ring
  rw [laplaceAt_convolutionSquare, hcoord]
  exact hpair

/-- The selected finite spectral prefix of the transported span is exactly
    the negative target multiplicity whenever the original detector square
    kills every other point of the prefix. -/
theorem finiteSpectralPrefix_re_eq_neg_xiMultiplicity_mul_sq_of_detectorSquare_zero_control
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) (lambda : Real)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (hg1 : laplaceAt g (rho.1 - 1 / 2) = 1)
    (hg2 : laplaceAt g (1 - star rho.1 - 1 / 2) = -1)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ S.erase rho →
      laplaceAt g.convolutionSquare (z.1 - 1 / 2) = 0) :
    (∑ z ∈ S,
      spectralTerm
        (annihilatorDetectorSpanVector (offlineZeroOrbitAnnihilator g rho.1) g lambda).convolutionSquare z).re =
      -(xiMultiplicity rho : Real) * lambda ^ 2 := by
  classical
  let v := annihilatorDetectorSpanVector (offlineZeroOrbitAnnihilator g rho.1) g lambda
  have hanchor :
      spectralTerm v.convolutionSquare rho =
        -(xiMultiplicity rho : Complex) * (lambda : Complex) ^ 2 := by
    unfold v spectralTerm centeredXiCoordinate
    rw [annihilatorDetectorSpanVector_convolutionSquare_laplaceAt_rho_sub_half_eq_neg_sq
      g rho.1 lambda hg1 hg2]
    ring
  have hother (z : sourceNontrivialZeroSet) (hz : z ∈ S.erase rho) :
      spectralTerm v.convolutionSquare z = 0 := by
    unfold spectralTerm centeredXiCoordinate
    rw [annihilatorDetectorSpanVector_convolutionSquare_laplaceAt_eq_zero_of_detectorSquare_eq_zero
      g rho.1 lambda (z.1 - 1 / 2) (hzero z hz)]
    simp
  have hrest :
      ∑ z ∈ S.erase rho, spectralTerm v.convolutionSquare z = 0 := by
    exact Finset.sum_eq_zero (fun z hz => hother z hz)
  have hsplit := Finset.sum_erase_add
    (s := S) (f := fun z : sourceNontrivialZeroSet => spectralTerm v.convolutionSquare z)
    (a := rho) hrho
  calc
    (∑ z ∈ S, spectralTerm v.convolutionSquare z).re =
        ((∑ z ∈ S.erase rho, spectralTerm v.convolutionSquare z) +
          spectralTerm v.convolutionSquare rho).re := by
      rw [hsplit]
    _ = (-(xiMultiplicity rho : Complex) * (lambda : Complex) ^ 2).re := by
      rw [hrest, zero_add, hanchor]
    _ = -(xiMultiplicity rho : Real) * lambda ^ 2 := by
      have hsquare : ((lambda : Complex) ^ 2).re = lambda ^ 2 := by
        rw [← Complex.ofReal_pow]
        exact Complex.ofReal_re _
      rw [Complex.mul_re]
      simp [hsquare]

end
end C1TwoPointSpectralPrefixTransport
end Source
end ConnesWeilRH
