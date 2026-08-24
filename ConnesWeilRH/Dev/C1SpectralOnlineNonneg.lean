/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SpectralWeil
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector

/-!
# C1SpectralOnlineNonneg - on-line spectral terms of a square

Stage-1 lemma W1 of the hqw sign attack
(`docs/proofs/1040_hqw_sign_attack.md`): for a source zero `rho` on the
critical line, the multiplicity-weighted spectral term of the Hermitian
convolution square is real and nonnegative, termwise, unconditionally — no
hypothesis on the test beyond compactness, no vanishing input, no RH claim.

The mechanism is the Hermitian square law `laplaceAt_convolutionSquare`
(`Dev/C1HealthyYoshidaDetector.lean:48`): at a purely imaginary centered
coordinate `w = rho - 1/2` one has `star w = -w`, so the law collapses to a
norm square `|laplaceAt g w|^2`, and the multiplicity weight is a natural
number.

This is the proven-positive block for the future splitting theorem (W3 in
1040); off-line zeros are deliberately not addressed here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralOnlineNonneg

open C1SpectralWeil
open C1HealthyYoshidaDetector
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- The centered coordinate of an on-line zero is purely imaginary:
`star w = -w`. -/
theorem centeredXiCoordinate_star_eq_neg_of_onLine
    (rho : sourceNontrivialZeroSet) (honline : rho.1.re = 1 / 2) :
    star (centeredXiCoordinate rho) = -(centeredXiCoordinate rho) := by
  apply Complex.ext <;> simp [centeredXiCoordinate, honline]

/-- **W1 (1040): the on-line spectral term of a Hermitian square is
nonnegative.**  Termwise in the spectral sum, unconditional in `g`. -/
theorem spectralTerm_convolutionSquare_nonneg_of_onLine
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (honline : rho.1.re = 1 / 2) :
    0 ≤ (spectralTerm g.convolutionSquare rho).re := by
  have hstar := centeredXiCoordinate_star_eq_neg_of_onLine rho honline
  unfold spectralTerm
  rw [laplaceAt_convolutionSquare, hstar, neg_neg]
  have hprod : star (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) *
      CompactLogTest.laplaceAt g (centeredXiCoordinate rho)
      = ((Complex.normSq
            (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.normSq, Complex.mul_re, Complex.mul_im] <;>
      first | ring | simp
  rw [hprod, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-! ### Axiom-cleanliness audit — both results are theorems; each depends
only on `[propext, Classical.choice, Quot.sound]`; no self-root, no
`sorryAx`, no new project axiom. -/
#print axioms centeredXiCoordinate_star_eq_neg_of_onLine
#print axioms spectralTerm_convolutionSquare_nonneg_of_onLine

end
end C1SpectralOnlineNonneg
end Source
end ConnesWeilRH
