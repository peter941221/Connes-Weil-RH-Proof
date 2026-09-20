/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1SpectralWeil

/-!
# C1SourceRHWeilConverse - the Weil converse oracle: SourceRH forces the
window archimedean face

This is the reverse arrow of the two-premise exit
`healthy_spectral_nonneg_sourceRH_of_yoshida_detector`
(C1CenterTwoRHExit.lean).  That theorem produces SourceRH from
[P1 detector] + [P2 spectral nonnegativity].  Here the same committed
ingredients are run backwards:

* SourceRH puts every source zero on the critical line, so the centered
  coordinate `centeredXiCoordinate rho` is purely imaginary.
* The Hermitian square law `laplaceAt_convolutionSquare` then reads each
  spectral term as `m * |laplaceAt g s|^2` with `m = xiMultiplicity rho`,
  so every spectral term has nonnegative real part.
* `Complex.re_tsum` and `tsum_nonneg` lift termwise nonnegativity to
  `0 <= spectralWeilValue (g.convolutionSquare)` under `SpectralSummable`.
* Gate 2 (`qw_eq_spectralWeilValue_centerTwo`, unconditional) and the
  window law `qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf`
  convert that into `archimedeanTerm (g.convolutionSquare) <= 0`.

Contrapositive (the F73 falsifier oracle, now formal): a single smooth
triple-vanishing window test with positive archimedean square refutes
SourceRH, as long as the square is spectrally summable.  RH is NOT claimed;
`SpectralSummable` is a hypothesis carried by the consumer, exactly as the
`C1SpectralWeil` contract requires.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SourceRHWeilConverse

open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open Complex
open C1SameOwnerWeil
open C1SpectralWeil
open C1HealthyYoshidaDetector
open C1CenterTwoCriterionBridge

noncomputable section

/-- A purely imaginary number is negated by the star involution. -/
theorem star_eq_neg_of_re_eq_zero (s : Complex) (h : s.re = 0) :
    star s = -s := by
  rw [Complex.star_def]
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, h]

/-- The centered coordinate of a critical-line zero is purely imaginary. -/
theorem re_centeredXiCoordinate_eq_zero (rho : ↥sourceNontrivialZeroSet)
    (hcl : RHDefinitionBridge.standard.sourceCriticalLine rho.1) :
    (centeredXiCoordinate rho).re = 0 := by
  have h := RHDefinitionBridge.standard.sourceCriticalLine_to_mathlib rho.1 hcl
  simp only [centeredXiCoordinate, Complex.sub_re]
  linarith [h, show ((1 / 2 : Complex)).re = (1 / 2 : Real) from by simp]

/-- On a critical-line zero the spectral term's real part is the
multiplicity times the squared transform value. -/
theorem spectralTerm_re_eq_mul_sq_of_sourceCriticalLine
    (g : CompactLogTest) (rho : ↥sourceNontrivialZeroSet)
    (hcl : RHDefinitionBridge.standard.sourceCriticalLine rho.1) :
    (spectralTerm g.convolutionSquare rho).re =
      (xiMultiplicity rho : Real) *
        Complex.normSq (CompactLogTest.laplaceAt g
          (centeredXiCoordinate rho)) := by
  have hxi := re_centeredXiCoordinate_eq_zero rho hcl
  have hstar : star (centeredXiCoordinate rho)
      = -(centeredXiCoordinate rho) := star_eq_neg_of_re_eq_zero _ hxi
  have hL : CompactLogTest.laplaceAt g.convolutionSquare
        (centeredXiCoordinate rho)
      = star (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) *
        CompactLogTest.laplaceAt g (centeredXiCoordinate rho) := by
    rw [laplaceAt_convolutionSquare, hstar, neg_neg]
  have hsq : star (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) *
      CompactLogTest.laplaceAt g (centeredXiCoordinate rho)
      = (Complex.normSq (CompactLogTest.laplaceAt g
        (centeredXiCoordinate rho)) : Complex) := by
    apply Complex.ext
    all_goals
      simp [Complex.normSq, Complex.conj_re, Complex.conj_im]
      try ring
  simp only [spectralTerm, hL, hsq]
  simp

/-- Termwise nonnegativity of the spectral real parts on the critical line. -/
theorem spectralTerm_re_nonneg_of_sourceCriticalLine
    (g : CompactLogTest) (rho : ↥sourceNontrivialZeroSet)
    (hcl : RHDefinitionBridge.standard.sourceCriticalLine rho.1) :
    0 ≤ (spectralTerm g.convolutionSquare rho).re := by
  rw [spectralTerm_re_eq_mul_sq_of_sourceCriticalLine g rho hcl]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- Termwise nonnegative real parts give a nonnegative spectral value
(the consumer carries `SpectralSummable`, per the `C1SpectralWeil` contract). -/
theorem spectralWeilValue_nonneg_of_termwise
    (F : CompactLogTest) (hSum : SpectralSummable F)
    (hall : ∀ rho : ↥sourceNontrivialZeroSet,
      0 ≤ (spectralTerm F rho).re) :
    0 ≤ spectralWeilValue F := by
  unfold spectralWeilValue
  rw [Complex.re_tsum hSum]
  exact tsum_nonneg hall

/-- SourceRH forces the centered spectral value nonnegative (under the
consumer's summability contract). -/
theorem spectralWeilValue_nonneg_of_sourceRH_of_spectralSummable
    (hRH : RHDefinitionBridge.SourceRH RHDefinitionBridge.standard)
    (g : CompactLogTest)
    (hSum : SpectralSummable g.convolutionSquare) :
    0 ≤ spectralWeilValue g.convolutionSquare := by
  have hall : ∀ rho : ↥sourceNontrivialZeroSet,
      0 ≤ (spectralTerm g.convolutionSquare rho).re := fun rho =>
    spectralTerm_re_nonneg_of_sourceCriticalLine g rho
      (RHDefinitionBridge.standard.sourceCriticalLine_to_mathlib rho.1
        (hRH rho.1 rho.property))
  exact spectralWeilValue_nonneg_of_termwise g.convolutionSquare hSum hall

/-- THE WEIL CONVERSE ORACLE.  SourceRH forces the archimedean face of the
window class nonpositive: for every smooth triple-vanishing test with root
support in `[-log 2 / 2, log 2 / 2]` and spectrally summable square,
`archimedeanTerm (g.convolutionSquare) <= 0`. -/
theorem archimedeanTerm_nonpos_of_sourceRH_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf
    (hRH : RHDefinitionBridge.SourceRH RHDefinitionBridge.standard)
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hSum : SpectralSummable g.convolutionSquare) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0 := by
  have h1 := qw_eq_spectralWeilValue_centerTwo g
  have h2 :=
    qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf
      g hvanishes hsupport
  have h3 := spectralWeilValue_nonneg_of_sourceRH_of_spectralSummable hRH g hSum
  rw [h2] at h1
  linarith

end

end C1SourceRHWeilConverse
end Source
end ConnesWeilRH
