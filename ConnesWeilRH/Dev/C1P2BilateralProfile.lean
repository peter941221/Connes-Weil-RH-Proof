import ConnesWeilRH.Dev.C1P2PrimePointMatching

/-!
# P2 bilateral observable profile

The same-owner Weil functional does not inspect a formula test at `y` and
`-y` independently.  Its finite-prime terms use their pair sum, and the
archimedean numerator uses the same pair sum together with the value at zero.
This leaf records that exact observable interface.  It is an algebraic
reduction only: it supplies no positivity and no RH conclusion.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2BilateralProfile

open MeasureTheory
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1LocalConfigurationDomination
open C1P2DefectZeroSumIdentity
open C1P2PrimePointMatching
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

/-- The bilateral profile actually observed by both the prime and archimedean
parts of the same-owner Weil functional. -/
def bilateralProfile (F : CompactLogTest) (y : ℝ) : ℂ :=
  F.test y + F.test (-y)

theorem primePairMatch_of_bilateralProfile_eq
    (F G : CompactLogTest)
    (hprofile : ∀ y : ℝ, bilateralProfile F y = bilateralProfile G y) :
    PrimePairMatch F G := by
  intro n hn
  exact hprofile (Real.log n)

theorem archimedeanNumerator_eq_of_bilateralProfile_eq
    (F G : CompactLogTest) (y : ℝ)
    (h0 : F.test 0 = G.test 0)
    (hprofile : ∀ y : ℝ, bilateralProfile F y = bilateralProfile G y) :
    archimedeanNumerator F y = archimedeanNumerator G y := by
  have hp := hprofile y
  dsimp [bilateralProfile] at hp
  unfold archimedeanNumerator
  rw [hp, h0]

theorem archimedeanIntegrand_eq_of_bilateralProfile_eq
    (F G : CompactLogTest)
    (h0 : F.test 0 = G.test 0)
    (hprofile : ∀ y : ℝ, bilateralProfile F y = bilateralProfile G y) :
    ∀ y : ℝ, archimedeanIntegrand F y = archimedeanIntegrand G y := by
  intro y
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_eq_of_bilateralProfile_eq F G y h0 hprofile]

theorem archimedeanTerm_eq_of_bilateralProfile_eq
    (F G : CompactLogTest)
    (h0 : F.test 0 = G.test 0)
    (hprofile : ∀ y : ℝ, bilateralProfile F y = bilateralProfile G y) :
    archimedeanTerm F = archimedeanTerm G := by
  have hi :
      (∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand F y) =
        ∫ y in Set.Ioi (0 : ℝ), archimedeanIntegrand G y := by
    apply integral_congr_ae
    filter_upwards with y
    exact archimedeanIntegrand_eq_of_bilateralProfile_eq F G h0 hprofile y
  unfold archimedeanTerm
  rw [h0, hi]

theorem finitePrimeSum_eq_of_bilateralProfile_eq
    (F G : CompactLogTest)
    (hprofile : ∀ y : ℝ, bilateralProfile F y = bilateralProfile G y) :
    finitePrimeSum F = finitePrimeSum G := by
  exact finitePrimeSum_eq_of_primePairMatch F G
    (primePairMatch_of_bilateralProfile_eq F G hprofile)

/-- If two triple-vanishing owners have the same complete bilateral profile
and the same origin value, the exact defect gate with those owners is zero.
This is a cancellation diagnostic, not a positivity theorem. -/
theorem defectGate_eq_zero_of_bilateralProfile_eq
    (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hWv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet W)
    (h0 : g.convolutionSquare.test 0 = W.convolutionSquare.test 0)
    (hprofile : ∀ y : ℝ,
      bilateralProfile g.convolutionSquare y =
        bilateralProfile W.convolutionSquare y) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) = 0 := by
  rw [defectGate_eq_archimedean_sub_of_primePairMatch g W hgv hWv
    (primePairMatch_of_bilateralProfile_eq g.convolutionSquare
      W.convolutionSquare hprofile)]
  rw [archimedeanTerm_eq_of_bilateralProfile_eq
    g.convolutionSquare W.convolutionSquare h0 hprofile]
  ring

end
end C1P2BilateralProfile
end Source
end ConnesWeilRH
