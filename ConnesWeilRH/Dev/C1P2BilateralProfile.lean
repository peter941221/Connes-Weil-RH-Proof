import ConnesWeilRH.Dev.C1P2PrimePointMatching
import ConnesWeilRH.Dev.C1GateMatrixRepresentation

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
open C1GateMatrixRepresentation
open Matrix
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open scoped BigOperators

noncomputable section

/-- The bilateral profile actually observed by both the prime and archimedean
parts of the same-owner Weil functional. -/
def bilateralProfile (F : CompactLogTest) (y : ℝ) : ℂ :=
  F.test y + F.test (-y)

/-! ### Canonical scalar for the aggregate producer -/

/- The producer-facing scalar is named separately from its later sign
   certificate.  This keeps the finite visible-prime owner fixed while
   leaving the source of its nonpositivity open. -/
noncomputable def p2AggregateValue (g : CompactLogTest) : ℝ :=
  archimedeanTerm g.convolutionSquare +
    ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
        (bilateralProfile g.convolutionSquare (Real.log n)).re

theorem p2AggregateValue_eq_archimedean_plus_finiteProfile (g : CompactLogTest) :
    p2AggregateValue g =
      archimedeanTerm g.convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re := by
  rfl

/-- On a genuine convolution square, the bilateral observable is twice the
real part of the positive-side value.  This is the Hermitian reduction used
by the semi-local trace owner. -/
theorem bilateralProfile_convolutionSquare_eq_two_re
    (g : CompactLogTest) (y : ℝ) :
    bilateralProfile g.convolutionSquare y =
      ((2 * (g.convolutionSquare.test y).re : ℝ) : ℂ) := by
  exact g.convolutionSquare_add_neg_eq_two_re y

theorem bilateralProfile_convolutionSquare_re_eq_two_re
    (g : CompactLogTest) (y : ℝ) :
    (bilateralProfile g.convolutionSquare y).re =
      2 * (g.convolutionSquare.test y).re := by
  rw [bilateralProfile_convolutionSquare_eq_two_re]
  simp

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

theorem finitePrimeTerm_nonpos_of_bilateralProfile_re_nonpos
    (F : CompactLogTest) {n : ℕ}
    (hprofile : (bilateralProfile F (Real.log n)).re ≤ 0) :
    finitePrimeTerm F n ≤ 0 := by
  rw [finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    hprofile

theorem finitePrimeSum_nonpos_of_bilateralProfile_re_nonpos
    (F : CompactLogTest)
    (hprofile : ∀ n ∈ globalPrimeIndexSet F,
      (bilateralProfile F (Real.log n)).re ≤ 0) :
    finitePrimeSum F ≤ 0 := by
  unfold finitePrimeSum
  exact Finset.sum_nonpos (fun n hn =>
    finitePrimeTerm_nonpos_of_bilateralProfile_re_nonpos F (hprofile n hn))

/-- Exact finite-prime readback as one weighted bilateral-profile sum.  This
is weaker than a pointwise profile sign and is the minimal aggregate target
for a detector-specific producer. -/
theorem finitePrimeSum_eq_bilateralProfile_weighted_sum
    (F : CompactLogTest) :
    finitePrimeSum F =
      ∑ n ∈ globalPrimeIndexSet F,
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (bilateralProfile F (Real.log n)).re := by
  unfold finitePrimeSum
  exact Finset.sum_congr rfl fun n hn =>
    finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re F n

theorem finitePrimeSum_eq_zero_of_visibleProfileMatch_to_primeFreeReference
    (g W : CompactLogTest)
    (hsupportW : Function.support W.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (hprofile : BilateralProfileMatchOn g.convolutionSquare
      W.convolutionSquare
      ((fun n : ℕ => Real.log (n : ℝ)) ''
        ((globalPrimeIndexSet g.convolutionSquare ∪
          globalPrimeIndexSet W.convolutionSquare : Finset ℕ) : Set ℕ))) :
    finitePrimeSum g.convolutionSquare = 0 := by
  have hmatch := finitePrimeSum_eq_of_bilateralProfileMatchOn_visible
    g.convolutionSquare W.convolutionSquare hprofile
  have hzero := finitePrimeSum_eq_zero_of_support_subset_open_log_two
    W.convolutionSquare hsupportW
  rw [hmatch, hzero]

theorem p2AggregateValue_eq_archimedean_of_visibleProfileMatch_to_primeFreeReference
    (g W : CompactLogTest)
    (hsupportW : Function.support W.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (hprofile : BilateralProfileMatchOn g.convolutionSquare
      W.convolutionSquare
      ((fun n : ℕ => Real.log (n : ℝ)) ''
        ((globalPrimeIndexSet g.convolutionSquare ∪
          globalPrimeIndexSet W.convolutionSquare : Finset ℕ) : Set ℕ))) :
    p2AggregateValue g = archimedeanTerm g.convolutionSquare := by
  have hzero := finitePrimeSum_eq_zero_of_visibleProfileMatch_to_primeFreeReference
    g W hsupportW hprofile
  rw [p2AggregateValue_eq_archimedean_plus_finiteProfile,
    ← finitePrimeSum_eq_bilateralProfile_weighted_sum, hzero, add_zero]

theorem archimedeanTerm_pos_of_healthyDetector_and_visibleProfileMatch_to_primeFreeReference
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (W : CompactLogTest)
    (hsupportW : Function.support W.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (hprofile : BilateralProfileMatchOn g.convolutionSquare
      W.convolutionSquare
      ((fun n : ℕ => Real.log (n : ℝ)) ''
        ((globalPrimeIndexSet g.convolutionSquare ∪
          globalPrimeIndexSet W.convolutionSquare : Finset ℕ) : Set ℕ))) :
    0 < archimedeanTerm g.convolutionSquare := by
  have hzero := finitePrimeSum_eq_zero_of_visibleProfileMatch_to_primeFreeReference
    g W hsupportW hprofile
  have hnegativeSpectral :
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
    (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
      hdata.weilSquareSumPositive
  have hnegative : C1SameOwnerWeil.qw g < 0 := by
    rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
    exact hnegativeSpectral
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hdata.vanishesOnF, hzero] at hnegative
  linarith

theorem p2AggregateValue_eq_ICgate_convolutionSquare (g : CompactLogTest) :
    p2AggregateValue g = ICgate g.convolutionSquare := by
  unfold p2AggregateValue ICgate
  rw [← finitePrimeSum_eq_bilateralProfile_weighted_sum]

theorem p2AggregateValue_spanObj_eq_gate_qform
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Set.Ioi (0 : ℝ))) :
    p2AggregateValue (spanObj w y) =
      y ⬝ᵥ (gateMatrix w *ᵥ y) := by
  rw [p2AggregateValue_eq_ICgate_convolutionSquare]
  exact gate_qform_span w y hw hI

theorem p2AggregateValue_spanObj_nonpos_of_negGateMatrix_posSemidef
    {k : ℕ} (w : Fin k → CompactLogTest) (y : Fin k → ℝ)
    {B : ℝ} (hw : ∀ i, Function.support (w i).test ⊆ Set.Ioo (-B) B)
    (hI : ∀ i j, IntegrableOn (archimedeanIntegrand (pairTest w i j))
      (Set.Ioi (0 : ℝ)))
    (hM : (-gateMatrix w).PosSemidef) :
    p2AggregateValue (spanObj w y) ≤ 0 := by
  rw [p2AggregateValue_spanObj_eq_gate_qform w y hw hI]
  have hq := hM.dotProduct_mulVec_nonneg y
  simpa [Matrix.mulVec, dotProduct] using hq

/-- The same readback with the Hermitian convolution-square profile written
directly as twice a real evaluation. -/
theorem finitePrimeSum_convolutionSquare_eq_two_re_weighted_sum
    (g : CompactLogTest) :
    finitePrimeSum g.convolutionSquare =
      ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (2 * (g.convolutionSquare.test (Real.log n)).re) := by
  rw [finitePrimeSum_eq_bilateralProfile_weighted_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [bilateralProfile_convolutionSquare_re_eq_two_re]

/-- Support-controlled version: the real aggregate can be evaluated on the
explicit finite cutoff supplied by the common-window prime-sum lemma. -/
theorem finitePrimeSum_convolutionSquare_eq_two_re_weighted_sum_range_of_support
    (g : CompactLogTest) {B : ℝ}
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-B) B) :
    finitePrimeSum g.convolutionSquare =
      ∑ n ∈ Finset.range (Nat.ceil (Real.exp B) + 1),
        ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
          (2 * (g.convolutionSquare.test (Real.log n)).re) := by
  have hpack := finitePrimeSum_packTest_eq_sum_range
    g.convolutionSquare.test g.convolutionSquare.compactSupport hsupport
  have hpackEq :
      packTest g.convolutionSquare.test g.convolutionSquare.compactSupport =
        g.convolutionSquare := by
    exact CompactLogTest.ext (by rfl)
  rw [hpackEq] at hpack
  rw [hpack]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re,
    bilateralProfile_convolutionSquare_re_eq_two_re]

/-! ### Minimal aggregate same-owner P2 sign consumer -/

/-- The archimedean term plus the exact finite weighted profile sum is the
minimal aggregate inequality implying `qw ≥ 0`.  No pointwise prime sign is
assumed. -/
theorem qw_nonneg_of_archimedean_plus_bilateralProfile_weighted_sum_nonpos
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hbalance :
      archimedeanTerm g.convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
          ArithmeticFunction.vonMangoldt n *
              (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0) :
    0 ≤ qw g := by
  have hprime := finitePrimeSum_eq_bilateralProfile_weighted_sum
    g.convolutionSquare
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hvanishes, hprime]
  linarith

/- The canonical scalar is exactly the negative of the same-owner Weil
   quadratic form on the healthy triple-vanishing owner. -/
theorem p2AggregateValue_eq_neg_qw_of_vanishes
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g) :
    p2AggregateValue g = -qw g := by
  rw [p2AggregateValue_eq_archimedean_plus_finiteProfile,
    ← finitePrimeSum_eq_bilateralProfile_weighted_sum]
  have hq := qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hvanishes
  linarith

theorem p2AggregateValue_nonpos_iff_qw_nonneg_of_vanishes
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g) :
    p2AggregateValue g ≤ 0 ↔ 0 ≤ qw g := by
  rw [p2AggregateValue_eq_neg_qw_of_vanishes g hvanishes]
  constructor <;> intro h <;> linarith

theorem p2AggregateValue_sub_eq_archimedean_sub_of_visibleProfileMatch
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
    p2AggregateValue g - p2AggregateValue W =
      archimedeanTerm g.convolutionSquare -
        archimedeanTerm W.convolutionSquare := by
  have hq := defectGate_eq_qw_sub g W hgv hWv
  have ha := defectGate_eq_archimedean_sub_of_primePairMatch
    g W hgv hWv
    (primePairMatch_of_bilateralProfileMatchOn_visible g.convolutionSquare
      W.convolutionSquare hprofile)
  calc
    p2AggregateValue g - p2AggregateValue W =
        C1SameOwnerWeil.qw W - C1SameOwnerWeil.qw g := by
      rw [p2AggregateValue_eq_neg_qw_of_vanishes g hgv,
        p2AggregateValue_eq_neg_qw_of_vanishes W hWv]
      ring
    _ = ICgate (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)) := hq.symm
    _ = archimedeanTerm g.convolutionSquare -
        archimedeanTerm W.convolutionSquare := ha

/-! The signed residual is available without cancelling the visible prime
    profile.  This is the route-1 replacement for exact prime-free matching. -/

theorem p2AggregateValue_sub_eq_defectGate
    (g W : CompactLogTest) :
    p2AggregateValue g - p2AggregateValue W =
      ICgate (ICdefect g.convolutionSquare {()}
        (fun _ => W.convolutionSquare) (fun _ => 1)) := by
  have hq := C1T2Assembly.defectGate_singleton_eq_sub g W
  calc
    p2AggregateValue g - p2AggregateValue W =
        ICgate g.convolutionSquare - ICgate W.convolutionSquare := by
      rw [p2AggregateValue_eq_ICgate_convolutionSquare,
        p2AggregateValue_eq_ICgate_convolutionSquare]
    _ = ICgate (ICdefect g.convolutionSquare {()}
          (fun _ => W.convolutionSquare) (fun _ => 1)) := hq.symm

theorem p2AggregateValue_eq_archimedean_plus_rangeProfile
    (g : CompactLogTest) {B : ℝ}
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-B) B) :
    p2AggregateValue g =
      archimedeanTerm g.convolutionSquare +
        ∑ n ∈ Finset.range (Nat.ceil (Real.exp B) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (2 * (g.convolutionSquare.test (Real.log n)).re) := by
  unfold p2AggregateValue
  rw [← finitePrimeSum_eq_bilateralProfile_weighted_sum,
    finitePrimeSum_convolutionSquare_eq_two_re_weighted_sum_range_of_support
      g hsupport]

/-- The aggregate profile inequality is not merely sufficient: on a
triple-vanishing owner it is exactly equivalent to the desired `qw ≥ 0`. -/
theorem qw_nonneg_iff_archimedean_plus_bilateralProfile_weighted_sum_nonpos
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g) :
    0 ≤ qw g ↔
      archimedeanTerm g.convolutionSquare +
        ∑ n ∈ globalPrimeIndexSet g.convolutionSquare,
          ArithmeticFunction.vonMangoldt n *
              (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0 := by
  have hprime := finitePrimeSum_eq_bilateralProfile_weighted_sum
    g.convolutionSquare
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hvanishes, hprime]
  constructor <;> intro h <;> linarith

/-! ### Direct same-owner P2 sign consumer -/

/- A detector-specific producer may establish the archimedean sign and the
   visible bilateral-profile sign independently.  The following consumer
   combines exactly those two premises through the healthy-owner Weil
   identity. -/
theorem qw_nonneg_of_archimedean_nonpos_and_visible_bilateralProfile_nonpos
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (harch : archimedeanTerm g.convolutionSquare ≤ 0)
    (hprofile : ∀ n ∈ globalPrimeIndexSet g.convolutionSquare,
      (bilateralProfile g.convolutionSquare (Real.log n)).re ≤ 0) :
    0 ≤ qw g := by
  have hprime : finitePrimeSum g.convolutionSquare ≤ 0 :=
    finitePrimeSum_nonpos_of_bilateralProfile_re_nonpos
      g.convolutionSquare hprofile
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
    g hvanishes]
  linarith

theorem bilateralProfile_eq_zero_of_test_odd
    (F : CompactLogTest)
    (hodd : ∀ x : ℝ, F.test (-x) = -F.test x) (y : ℝ) :
    bilateralProfile F y = 0 := by
  unfold bilateralProfile
  rw [hodd y]
  ring

theorem finitePrimeTerm_eq_zero_of_test_odd
    (F : CompactLogTest)
    (hodd : ∀ x : ℝ, F.test (-x) = -F.test x) (n : ℕ) :
    finitePrimeTerm F n = 0 := by
  rw [finitePrimeTerm_eq_realCoefficient_mul_bilateralProfile_re,
    bilateralProfile_eq_zero_of_test_odd F hodd]
  simp

theorem finitePrimeSum_eq_zero_of_test_odd
    (F : CompactLogTest)
    (hodd : ∀ x : ℝ, F.test (-x) = -F.test x) :
    finitePrimeSum F = 0 := by
  unfold finitePrimeSum
  exact Finset.sum_eq_zero (fun n hn =>
    finitePrimeTerm_eq_zero_of_test_odd F hodd n)

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
