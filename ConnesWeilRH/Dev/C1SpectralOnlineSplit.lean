/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SpectralOnlineNonneg

/-!
# C1SpectralOnlineSplit - the unconditional W3 spectral split

For an absolutely summable spectral series, this module separates the exact
critical-line contribution from its complementary off-line contribution.
The critical-line mass is nonnegative term by term by W1.  The complementary
mass is deliberately kept as a named residual: the current source API exposes
the functional-equation transport `rho |-> 1 - rho`, but it does not yet
provide the conjugate-zero transport needed to identify every Hermitian
partner with a single `oneSubXiZero` representative.  No pairing shortcut is
silently introduced here.

The result is an exact identity under `SpectralSummable`; it is not a proof of
the off-line residual bound, finite-vanishing positivity, or RH.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralOnlineSplit

open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1SpectralOnlineNonneg

noncomputable section

/-! ### Exact index split -/

/-- The exact source spectral indices lying on the critical line. -/
def onLineZeroSet : Set sourceNontrivialZeroSet :=
  {rho | rho.1.re = 1 / 2}

/-- The complementary source spectral indices. -/
def offLineZeroSet : Set sourceNontrivialZeroSet := onLineZeroSetᶜ

/-- The spectral summand retained by the critical-line block. -/
noncomputable def onLineSpectralTerm
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) : Complex :=
  onLineZeroSet.indicator (spectralTerm g.convolutionSquare) rho

/-- The spectral summand retained by the off-line residual. -/
noncomputable def offLineSpectralTerm
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) : Complex :=
  offLineZeroSet.indicator (spectralTerm g.convolutionSquare) rho

/-- The real critical-line spectral mass. -/
noncomputable def onLineSpectralMass (g : CompactLogTest) : Real :=
  (∑' rho : sourceNontrivialZeroSet, onLineSpectralTerm g rho).re

/-- The real off-line spectral residual. -/
noncomputable def offLineSpectralMass (g : CompactLogTest) : Real :=
  (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho).re

theorem onLineSpectralTerm_add_offLineSpectralTerm
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    onLineSpectralTerm g rho + offLineSpectralTerm g rho =
      spectralTerm g.convolutionSquare rho := by
  by_cases h : rho ∈ onLineZeroSet
  · have hcomp : rho ∉ offLineZeroSet := by
      simpa [offLineZeroSet] using h
    simp [onLineSpectralTerm, offLineSpectralTerm, h, hcomp]
  · have hcomp : rho ∈ offLineZeroSet := by
      simpa [offLineZeroSet] using h
    simp [onLineSpectralTerm, offLineSpectralTerm, h, hcomp]

theorem summable_onLineSpectralTerm
    (g : CompactLogTest) (hF : SpectralSummable g.convolutionSquare) :
    Summable (onLineSpectralTerm g) := by
  exact hF.indicator onLineZeroSet

theorem summable_offLineSpectralTerm
    (g : CompactLogTest) (hF : SpectralSummable g.convolutionSquare) :
    Summable (offLineSpectralTerm g) := by
  exact hF.indicator offLineZeroSet

/-- W1 lifts from termwise nonnegativity to a nonnegative total mass on the
critical line. -/
theorem onLineSpectralMass_nonnegative_of_summable
    (g : CompactLogTest) (hF : SpectralSummable g.convolutionSquare) :
    0 ≤ onLineSpectralMass g := by
  have hsum : Summable (onLineSpectralTerm g) :=
    summable_onLineSpectralTerm g hF
  unfold onLineSpectralMass
  rw [Complex.re_tsum hsum]
  apply tsum_nonneg
  intro rho
  by_cases h : rho ∈ onLineZeroSet
  · have hterm := spectralTerm_convolutionSquare_nonneg_of_onLine
      g rho (by simpa [onLineZeroSet] using h)
    simpa [onLineSpectralTerm, h] using hterm
  · simp [onLineSpectralTerm, h]

/-- **W3 exact split.**  The spectral Weil value is the sum of its
critical-line mass and the complementary off-line residual. -/
theorem spectralWeilValue_eq_onLineSpectralMass_add_offLineSpectralMass
    (g : CompactLogTest) (hF : SpectralSummable g.convolutionSquare) :
    C1SpectralWeil.spectralWeilValue g.convolutionSquare =
      onLineSpectralMass g + offLineSpectralMass g := by
  have honline : Summable (onLineSpectralTerm g) :=
    summable_onLineSpectralTerm g hF
  have hoffline : Summable (offLineSpectralTerm g) :=
    summable_offLineSpectralTerm g hF
  have hsum : (fun rho : sourceNontrivialZeroSet =>
      onLineSpectralTerm g rho + offLineSpectralTerm g rho) =
      spectralTerm g.convolutionSquare := by
    funext rho
    exact onLineSpectralTerm_add_offLineSpectralTerm g rho
  change (∑' rho : sourceNontrivialZeroSet,
      spectralTerm g.convolutionSquare rho).re =
    (∑' rho : sourceNontrivialZeroSet, onLineSpectralTerm g rho).re +
      (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho).re
  have htsum :
      (∑' rho : sourceNontrivialZeroSet,
        (onLineSpectralTerm g rho + offLineSpectralTerm g rho)) =
        (∑' rho : sourceNontrivialZeroSet, onLineSpectralTerm g rho) +
          (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho) :=
    (honline.hasSum.add hoffline.hasSum).tsum_eq
  rw [← hsum, htsum]
  rfl

/-! ### Functional-equation coordinates: pairing remains explicit -/

/-- The existing functional-equation representative reflects the centered
coordinate by a sign.  This is not yet the conjugate reflection used by the
Hermitian square law, so the two notions must remain distinct. -/
theorem centeredXiCoordinate_oneSubXiZero
    (rho : sourceNontrivialZeroSet) :
    centeredXiCoordinate (oneSubXiZero rho) =
      -centeredXiCoordinate rho := by
  apply Complex.ext
  · simp [centeredXiCoordinate, oneSubXiZero_coe]
    ring
  · simp [centeredXiCoordinate, oneSubXiZero_coe]

theorem xiMultiplicity_oneSubXiZero_eq
    (rho : sourceNontrivialZeroSet) :
    xiMultiplicity (oneSubXiZero rho) = xiMultiplicity rho :=
  xiMultiplicity_oneSub rho

/-! ### Axiom-cleanliness audit -/
#print axioms onLineSpectralTerm_add_offLineSpectralTerm
#print axioms summable_onLineSpectralTerm
#print axioms summable_offLineSpectralTerm
#print axioms onLineSpectralMass_nonnegative_of_summable
#print axioms spectralWeilValue_eq_onLineSpectralMass_add_offLineSpectralMass
#print axioms centeredXiCoordinate_oneSubXiZero
#print axioms xiMultiplicity_oneSubXiZero_eq

end
end C1SpectralOnlineSplit
end Source
end ConnesWeilRH
