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
open CCM25Concrete.SelectedWeilSquare
open scoped BigOperators

noncomputable section

/-- The bilateral profile actually observed by both the prime and archimedean
parts of the same-owner Weil functional. -/
def bilateralProfile (F : CompactLogTest) (y : ℝ) : ℂ :=
  F.test y + F.test (-y)

/-- A profile equality restricted to a set of log-coordinates.  This is the
finite-sample form used by the visible-prime sum, as opposed to equality on
the whole real line. -/
def BilateralProfileMatchOn (F G : CompactLogTest) (S : Set ℝ) : Prop :=
  ∀ y ∈ S, bilateralProfile F y = bilateralProfile G y

theorem primePairMatch_of_bilateralProfileMatchOn_visible
    (F G : CompactLogTest)
    (hprofile : BilateralProfileMatchOn F G
      ((fun n : ℕ => Real.log (n : ℝ)) ''
        ((globalPrimeIndexSet F ∪ globalPrimeIndexSet G : Finset ℕ) : Set ℕ))) :
    PrimePairMatch F G := by
  intro n hn
  exact hprofile (Real.log n) (by exact ⟨n, hn, rfl⟩)

theorem finitePrimeSum_eq_of_bilateralProfileMatchOn_visible
    (F G : CompactLogTest)
    (hprofile : BilateralProfileMatchOn F G
      ((fun n : ℕ => Real.log (n : ℝ)) ''
        ((globalPrimeIndexSet F ∪ globalPrimeIndexSet G : Finset ℕ) : Set ℕ))) :
    finitePrimeSum F = finitePrimeSum G := by
  exact finitePrimeSum_eq_of_primePairMatch F G
    (primePairMatch_of_bilateralProfileMatchOn_visible F G hprofile)

theorem finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re
    (F : CompactLogTest) (n : ℕ) :
    finitePrimeTerm F n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (bilateralProfile F (Real.log n)).re := by
  unfold finitePrimeTerm finitePrimeTermComplex bilateralProfile
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_mul, zero_sub]
  ring

theorem finitePrimeTerm_nonneg_of_bilateralProfile_re_nonneg
    (F : CompactLogTest) {n : ℕ}
    (hprofile : 0 ≤ (bilateralProfile F (Real.log n)).re) :
    0 ≤ finitePrimeTerm F n := by
  rw [finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re]
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    hprofile

theorem finitePrimeSum_nonneg_of_bilateralProfile_re_nonneg
    (F : CompactLogTest)
    (hprofile : ∀ n ∈ globalPrimeIndexSet F,
      0 ≤ (bilateralProfile F (Real.log n)).re) :
    0 ≤ finitePrimeSum F := by
  unfold finitePrimeSum
  exact Finset.sum_nonneg (fun n hn =>
    finitePrimeTerm_nonneg_of_bilateralProfile_re_nonneg F (hprofile n hn))

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

theorem archimedeanNumerator_sub_eq_of_bilateralProfile
    (F G : CompactLogTest) (y : ℝ) :
    archimedeanNumerator F y - archimedeanNumerator G y =
      Complex.ofRealCLM (Real.exp (y / 2)) *
          (bilateralProfile F y - bilateralProfile G y) -
        2 * (F.test 0 - G.test 0) := by
  unfold archimedeanNumerator bilateralProfile
  ring

theorem archimedeanIntegrand_sub_eq_of_bilateralProfile
    (F G : CompactLogTest) (y : ℝ) :
    archimedeanIntegrand F y - archimedeanIntegrand G y =
      (Complex.ofRealCLM (Real.exp (y / 2)) *
          (bilateralProfile F y - bilateralProfile G y) -
        2 * (F.test 0 - G.test 0)) /
        (SelectedWeilSquareOwner.archimedeanDenominator y : ℂ) := by
  unfold archimedeanIntegrand
  rw [← sub_div, archimedeanNumerator_sub_eq_of_bilateralProfile]

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

theorem defectGate_eq_archimedean_sub_of_bilateralProfileMatchOn_visible
    (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hWv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet W)
    (hprofile : BilateralProfileMatchOn g.convolutionSquare
      W.convolutionSquare
      ((fun n : ℕ => Real.log (n : ℝ)) ''
        ((globalPrimeIndexSet g.convolutionSquare ∪
          globalPrimeIndexSet W.convolutionSquare : Finset ℕ) : Set ℕ))) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) =
      archimedeanTerm g.convolutionSquare -
        archimedeanTerm W.convolutionSquare := by
  exact defectGate_eq_archimedean_sub_of_primePairMatch g W hgv hWv
    (primePairMatch_of_bilateralProfileMatchOn_visible
      g.convolutionSquare W.convolutionSquare hprofile)

end
end C1P2BilateralProfile
end Source
end ConnesWeilRH
