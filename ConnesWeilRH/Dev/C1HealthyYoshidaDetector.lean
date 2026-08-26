import ConnesWeilRH.Dev.C1CenterTwoRHExit
import ConnesWeilRH.Source.CC20YoshidaConvolution
import ConnesWeilRH.Source.CC20YoshidaFullProduct

/-!
# C1HealthyYoshidaDetector - detector scaffold on the healthy compact-log owner

The capstone `healthy_spectral_nonneg_sourceRH_of_yoshida_detector` leaves two
premises.  This module refines premise `1` (Yoshida detector existence) into
concrete finite data and supplies the first structural lemma for the future
construction.

Unlike the normalized concrete algebra, whose `convolutionSquare` doubles the
Mellin value (`not_normalizedCC20MellinConvolutionLaw`), the healthy owner's
square is the genuine Hermitian square `g.involution.convolution g`, so the
bilateral Laplace transform pairs the two pole moments of the root:

```text
laplaceAt (g.convolutionSquare) s = conj (laplaceAt g (-conj s)) * laplaceAt g s
```

Consequently a test vanishing at the right pole image `s = 1/2` kills the
ENTIRE pole term of its square (the pairing takes both pole moments at once),
and on every triple-vanishing test the Weil functional reduces to the clean
archimedean-plus-finite remainder.

The detector data package below is the healthy analogue of the normalized
`ConcreteYoshidaMomentData`: three nondegeneracy fields plus an unconditional
positivity field for the square's local sum.  Producing this package for every
off-line source zero is the remaining constructive work; it is NOT produced
here. RH is NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaDetector

open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open C1SameOwnerWeil
open C1CenterTwoCriterionBridge
open C1CenterTwoRHExit

/-! ### The Hermitian square law -/

/-- The genuine convolution square law: the Hermitian square of the root
multiplies the paired transform values. -/
theorem laplaceAt_convolutionSquare (g : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt g.convolutionSquare s =
      star (CompactLogTest.laplaceAt g (-star s)) *
        CompactLogTest.laplaceAt g s := by
  rw [CompactLogTest.convolutionSquare, CompactLogTest.laplaceAt_convolution,
    CompactLogTest.laplaceAt_involution]

/-- On real evaluation points the Hermitian square pairs the two pole moments
of the root. -/
theorem laplaceAt_convolutionSquare_ofReal (g : CompactLogTest) (x : ℝ) :
    CompactLogTest.laplaceAt g.convolutionSquare ((x : ℂ)) =
      star (CompactLogTest.laplaceAt g (-(x : ℂ))) *
        CompactLogTest.laplaceAt g ((x : ℂ)) := by
  rw [laplaceAt_convolutionSquare]
  congr 1
  simp [Complex.conj_ofReal]

/-- The half-point pairing form in the native complex literals. -/
theorem laplaceAt_convolutionSquare_half (g : CompactLogTest) :
    CompactLogTest.laplaceAt g.convolutionSquare (1 / 2 : ℂ) =
      star (CompactLogTest.laplaceAt g (-(1 / 2 : ℂ))) *
        CompactLogTest.laplaceAt g (1 / 2 : ℂ) := by
  have hk := laplaceAt_convolutionSquare_ofReal g (1 / 2 : ℝ)
  rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) from by
      push_cast; ring] at hk
  exact hk

/-- The reflected half-point pairing form in the native complex literals. -/
theorem laplaceAt_convolutionSquare_neg_half (g : CompactLogTest) :
    CompactLogTest.laplaceAt g.convolutionSquare (-1 / 2 : ℂ) =
      star (CompactLogTest.laplaceAt g (1 / 2 : ℂ)) *
        CompactLogTest.laplaceAt g (-1 / 2 : ℂ) := by
  have hk := laplaceAt_convolutionSquare_ofReal g (-(1 / 2 : ℝ))
  rw [Complex.ofReal_neg, neg_neg,
    show -((1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) from by
      push_cast; ring,
    show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) from by
      push_cast; ring] at hk
  exact hk

/-! ### The pole term of a Hermitian square -/

/-- Vanishing at the right pole image kills both pole moments of the square at
once, because the Hermitian pairing needs only one of the two factors. -/
theorem poleTerm_convolutionSquare_of_laplaceAt_half_eq_zero
    (g : CompactLogTest)
    (h : CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0) :
    C1SameOwnerWeil.poleTerm g.convolutionSquare = 0 := by
  rw [C1SameOwnerWeil.poleTerm,
    laplaceAt_convolutionSquare_half,
    laplaceAt_convolutionSquare_neg_half,
    h, mul_zero, star_zero, zero_mul]
  simp

/-- A triple-vanishing healthy test has zero pole term on its square. -/
theorem poleTerm_convolutionSquare_of_vanishesOn_cc20Triple
    (g : CompactLogTest)
    (h : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    C1SameOwnerWeil.poleTerm g.convolutionSquare = 0 := by
  refine poleTerm_convolutionSquare_of_laplaceAt_half_eq_zero g ?_
  simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
    h CriticalVanishingPoint.half (by simp [cc20TripleFiniteVanishingSet])

/-- On triple-vanishing tests the whole same-owner Weil functional is the
negative archimedean-plus-finite remainder. -/
theorem qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    (g : CompactLogTest)
    (h : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    C1SameOwnerWeil.qw g =
      -(C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) -
        C1SameOwnerWeil.finitePrimeSum g.convolutionSquare := by
  rw [C1SameOwnerWeil.qw_eq_psi_square, C1SameOwnerWeil.psi_eq_components,
    poleTerm_convolutionSquare_of_vanishesOn_cc20Triple g h]
  ring

/-- If the Hermitian square is prime-free by support, triple vanishing leaves
only the negative archimedean contribution in the same-owner Weil value. -/
theorem qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2)) :
    C1SameOwnerWeil.qw g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare := by
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hvanishes,
    C1SameOwnerWeil.finitePrimeSum_eq_zero_of_support_subset_open_log_two
      g.convolutionSquare hsupport]
  ring

/-- Root support in the full Yoshida window `[−log 2 / 2, log 2 / 2]` already
places the Hermitian square in the open prime-free window `(-log 2, log 2)`,
because the doubled endpoints carry no mass.  Triple vanishing then leaves
only the negative archimedean contribution. -/
theorem qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    C1SameOwnerWeil.qw g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare := by
  refine qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    g hvanishes ?_
  have hwindow :=
    CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g hsupport
  have htwo : (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 := by ring
  rw [htwo] at hwindow
  exact hwindow

/-- The interface the endpoint sign theorem must fill: once the archimedean
term is known nonpositive on the centered root-support class (the
Yoshida / Connes-Consani endpoint at `log 2 / 2`), the same-owner Weil value
is nonnegative there. -/
theorem qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (harch : C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf
    g hvanishes hsupport]
  linarith

/-! ### The detector data package -/

/-- The healthy detector data package: three nondegeneracy fields plus an
unconditional positivity field for the square's local Weil sum.  This is the
healthy analogue of the normalized `ConcreteYoshidaMomentData`. -/
structure HealthyYoshidaDetectorData (rho : ℂ) (g : CompactLogTest) : Prop where
  compactSupportSmooth :
    C1.healthyCC20TestSpace.compactSupportSmooth g
  vanishesOnF :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g
  detectsRho : CompactLogTest.laplaceAt g rho ≠ 0
  weilSquareSumPositive :
    0 < C1.healthyCC20TestSpace.weilLocalSum
        (C1.healthyCC20TestSpace.starConvolution g)

/-- The sign field is negativity of the independently defined spectral value
of the square, via the closed center-`2` Gate 2 chain. -/
theorem weilSquareSumPositive_iff_spectralWeilValue_neg
    (g : CompactLogTest) :
    (0 < C1.healthyCC20TestSpace.weilLocalSum
        (C1.healthyCC20TestSpace.starConvolution g)) ↔
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 := by
  rw [C1.healthyWeilSquareReadoff, qw_eq_spectralWeilValue_centerTwo]
  constructor <;> intro h <;> linarith

/-- On a triple-vanishing prime-free square, the detector's local Weil
positivity is exactly strict positivity of the remaining archimedean term. -/
theorem weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2)) :
    (0 < C1.healthyCC20TestSpace.weilLocalSum
        (C1.healthyCC20TestSpace.starConvolution g)) ↔
      0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare := by
  rw [C1.healthyWeilSquareReadoff,
    qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
      g hvanishes hsupport]
  constructor <;> intro h <;> linarith

/-- Detector data packs into the generic Yoshida detector on the healthy
owner. -/
theorem nonempty_yoshidaDetector_of_healthyDetectorData
    {rho : ℂ} {g : CompactLogTest}
    (hg : HealthyYoshidaDetectorData rho g) :
    Nonempty (YoshidaDetector C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet rho) :=
  Nonempty.intro
    { test := g
      compactSupportSmooth := hg.compactSupportSmooth
      vanishesOnF := hg.vanishesOnF
      detectsRho := hg.detectsRho
      weilSumPositiveIfOffLine := fun _hrho _hoff =>
        hg.weilSquareSumPositive }

/-- Detector data for every off-line source zero yields detector existence on
the healthy owner. -/
theorem healthyCC20YoshidaDetectorExists_of_healthyDetectorData
    (h : ∀ {rho : ℂ},
      RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re ≠ 1 / 2 →
          ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho g) :
    CC20YoshidaDetectorExists C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  intro rho hrho hoff
  rcases h hrho hoff with ⟨g, hg⟩
  exact nonempty_yoshidaDetector_of_healthyDetectorData hg

/-- Refined capstone: `SourceRH` follows from detector data for every off-line
source zero plus the spectral sign premise. -/
theorem healthy_sourceRH_of_healthyDetectorData_and_spectral_nonneg
    (h : ∀ {rho : ℂ},
      RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re ≠ 1 / 2 →
          ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho g)
    (hsign : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g →
        0 ≤ C1SpectralWeil.spectralWeilValue g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH :=
  healthy_spectral_nonneg_sourceRH_of_yoshida_detector
    (healthyCC20YoshidaDetectorExists_of_healthyDetectorData h) hsign

end C1HealthyYoshidaDetector
end Source
end ConnesWeilRH
