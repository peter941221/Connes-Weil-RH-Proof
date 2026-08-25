import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1SpectralHermitianPartner
import ConnesWeilRH.Dev.C1SpectralOnlineNonneg
import ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplit

/-!
# C1SpectralRealPair - the phase-route foundations for W4b-bound

KT-1040c showed the modulus-form sufficient condition is false on the bounded
witness family while the real-phase injections stay nearly neutral
(`docs/proofs/1042_kt1040c_probe.py`): the W4b-bound attack surface is the
PHASE structure of the Hermitian pair product.  This leaf lays the two formal
foundations that attack needs:

1. For a REAL test (`IsRealTest`: pointwise fixed by conjugation) the
   conjugation leg of the Hermitian square law collapses: the off-line pair
   product becomes the explicit product `L_g (-w) * L_g w` - the object whose
   phase must be controlled.  The numerical witness family `g = P(D) h`
   (KT-1040a/b/c) is pointwise real, so this is the operative shape.

2. The exact origin-mass readback for `F = g □` (no reality needed): the
   square's value at zero is a nonnegative real and its norm is the integrated
   squared norm of the root test.  A pointwise off-origin autocorrelation bound
   is deliberately left as a separate analysis obligation; it does not follow
   from this readback alone.

Consumer on the coverage chain: W4b-bound
(`hqw_of_forall_vanishing_rightHalf_bound`,
`Dev/C1SpectralQwAssembly.lean`); the arithmetic binding
`onLine_add_offLine_eq_neg_archimedeanTerm_sub_finitePrimeSum` is the identity
these foundations attack.  No RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralRealPair

open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open C1SpectralWeil
open C1SpectralHermitianPartner
open C1SpectralOnlineNonneg
open C1SpectralOnlineSplit
open C1SpectralOfflinePairing
open C1SpectralQwAssembly
open C1XiCenterTwoGammaComplexSplit
open MeasureTheory
open Filter

noncomputable section

/-! ### Real tests: the conjugation leg collapses -/

/-- A compact log test whose point values are fixed by conjugation.  The
numerical witness family of KT-1040a/b/c has this property. -/
def IsRealTest (g : CompactLogTest) : Prop :=
  ∀ x : ℝ, star (g.test x) = g.test x

/-! ### Constructible real component owners -/

theorem isRealTest_realPartTest (g : CompactLogTest) :
    IsRealTest (realPartTest g) := by
  intro x
  rw [realPartTest_apply]
  simp

theorem isRealTest_imagPartTest (g : CompactLogTest) :
    IsRealTest (imagPartTest g) := by
  intro x
  rw [imagPartTest_apply]
  simp

theorem realPartTest_vanishesOn_of_vanishesOn
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    CC20VanishesOn C1.healthyCC20TestSpace F (realPartTest g) := by
  intro p hp
  cases p with
  | zero =>
      have hg := hvanishes CriticalVanishingPoint.zero hp
      have hr := laplaceAt_realPart_eq_zero_of_eq_zero
        (s := (0 : ℝ)) (g := g) (by simpa [C1.healthyMellinReadoff,
          criticalVanishingPointValue] using hg)
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hr
  | half =>
      have hg := hvanishes CriticalVanishingPoint.half hp
      have hg' : CompactLogTest.laplaceAt g ((1 / 2 : ℝ) : ℂ) = 0 := by
        simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hg
      have hr := laplaceAt_realPart_eq_zero_of_eq_zero
        (s := (1 / 2 : ℝ)) (g := g) hg'
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hr
  | one =>
      have hg := hvanishes CriticalVanishingPoint.one hp
      have hr := laplaceAt_realPart_eq_zero_of_eq_zero
        (s := (1 : ℝ)) (g := g) (by simpa [C1.healthyMellinReadoff,
          criticalVanishingPointValue] using hg)
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hr

theorem imagPartTest_vanishesOn_of_vanishesOn
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    CC20VanishesOn C1.healthyCC20TestSpace F (imagPartTest g) := by
  intro p hp
  cases p with
  | zero =>
      have hg := hvanishes CriticalVanishingPoint.zero hp
      have hi := laplaceAt_imagPart_eq_zero_of_eq_zero
        (s := (0 : ℝ)) (g := g) (by simpa [C1.healthyMellinReadoff,
          criticalVanishingPointValue] using hg)
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hi
  | half =>
      have hg := hvanishes CriticalVanishingPoint.half hp
      have hg' : CompactLogTest.laplaceAt g ((1 / 2 : ℝ) : ℂ) = 0 := by
        simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hg
      have hi := laplaceAt_imagPart_eq_zero_of_eq_zero
        (s := (1 / 2 : ℝ)) (g := g) hg'
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hi
  | one =>
      have hg := hvanishes CriticalVanishingPoint.one hp
      have hi := laplaceAt_imagPart_eq_zero_of_eq_zero
        (s := (1 : ℝ)) (g := g) (by simpa [C1.healthyMellinReadoff,
          criticalVanishingPointValue] using hg)
      simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using hi

/-! ### Exact complex-to-real spectral split -/

theorem laplaceAt_convolutionSquare_eq_componentSquares_add_cross
    (g : CompactLogTest) (s : ℂ) :
    CompactLogTest.laplaceAt g.convolutionSquare s =
      CompactLogTest.laplaceAt (realPartTest g).convolutionSquare s +
        CompactLogTest.laplaceAt (imagPartTest g).convolutionSquare s +
        Complex.I *
          (star (CompactLogTest.laplaceAt (realPartTest g) (-star s)) *
              CompactLogTest.laplaceAt (imagPartTest g) s -
            star (CompactLogTest.laplaceAt (imagPartTest g) (-star s)) *
              CompactLogTest.laplaceAt (realPartTest g) s) := by
  rw [C1HealthyYoshidaDetector.laplaceAt_convolutionSquare,
    laplaceAt_eq_realPart_add_I_imagPart g (-star s),
    laplaceAt_eq_realPart_add_I_imagPart g s,
    C1HealthyYoshidaDetector.laplaceAt_convolutionSquare,
    C1HealthyYoshidaDetector.laplaceAt_convolutionSquare]
  simp only [map_add, map_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

/-- Pointwise conjugation identity for the exponential-weight integrand of a
real test. -/
theorem star_expMul_test (g : CompactLogTest) (hreal : IsRealTest g) (s : ℂ)
    (x : ℝ) :
    star (Complex.exp (s * (x : ℂ)) * g.test x) =
      Complex.exp (star s * (x : ℂ)) * g.test x := by
  change (starRingEnd ℂ)
      (Complex.exp (s * (x : ℂ)) * g.test x) =
    Complex.exp (star s * (x : ℂ)) * g.test x
  rw [map_mul, ← Complex.exp_conj]
  rw [show (starRingEnd ℂ) (s * (x : ℂ)) = star s * (x : ℂ) by
    rw [map_mul]
    simp]
  exact congrArg (fun z : ℂ => Complex.exp (star s * (x : ℂ)) * z)
    (hreal x)

/-- Conjugation commutes with the bilateral Laplace evaluation of a real
test: the star can be pushed onto the evaluation point. -/
theorem laplaceAt_star (g : CompactLogTest) (hreal : IsRealTest g) (s : ℂ) :
    star (CompactLogTest.laplaceAt g s) =
      CompactLogTest.laplaceAt g (star s) := by
  unfold CompactLogTest.laplaceAt
  simp only [CC20YoshidaConvolution.CompactLogTest.exponentialWeight_apply]
  calc
    star (∫ x : ℝ,
        Complex.exp (s * (x : ℂ)) * g.test x) =
        ∫ x : ℝ, star (Complex.exp (s * (x : ℂ)) * g.test x) :=
      (integral_conj).symm
    _ = ∫ x : ℝ, Complex.exp (star s * (x : ℂ)) * g.test x :=
      MeasureTheory.integral_congr_ae
        (ae_of_all _ (fun x => star_expMul_test g hreal s x))

/-- A real test has a real Laplace value at every real spectral point. -/
theorem laplaceAt_im_eq_zero_of_isRealTest_real
    (g : CompactLogTest) (hreal : IsRealTest g) (s : ℝ) :
    (CompactLogTest.laplaceAt g (s : ℂ)).im = 0 := by
  have hstar := laplaceAt_star g hreal (s : ℂ)
  have hfixed : star (CompactLogTest.laplaceAt g (s : ℂ)) =
      CompactLogTest.laplaceAt g (s : ℂ) := by
    simpa using hstar
  have him := congrArg Complex.im hfixed
  have him' : -(CompactLogTest.laplaceAt g (s : ℂ)).im =
      (CompactLogTest.laplaceAt g (s : ℂ)).im := by
    simpa [Complex.star_def] using him
  linarith

/-- At a real spectral point, the explicit cross term in the complex-to-real
split is purely imaginary.  This is an exact reality statement, not a global
positivity estimate. -/
theorem laplaceAt_convolutionSquare_cross_re_zero_at_real
    (g : CompactLogTest) (s : ℝ) :
    (Complex.I *
      (star (CompactLogTest.laplaceAt (realPartTest g) (-star (s : ℂ))) *
          CompactLogTest.laplaceAt (imagPartTest g) (s : ℂ) -
        star (CompactLogTest.laplaceAt (imagPartTest g) (-star (s : ℂ))) *
          CompactLogTest.laplaceAt (realPartTest g) (s : ℂ))).re = 0 := by
  have hrealR := isRealTest_realPartTest g
  have hrealI := isRealTest_imagPartTest g
  have hRpos := laplaceAt_im_eq_zero_of_isRealTest_real
    (realPartTest g) hrealR s
  have hIpos := laplaceAt_im_eq_zero_of_isRealTest_real
    (imagPartTest g) hrealI s
  have hRneg := laplaceAt_im_eq_zero_of_isRealTest_real
    (realPartTest g) hrealR (-s)
  have hIneg := laplaceAt_im_eq_zero_of_isRealTest_real
    (imagPartTest g) hrealI (-s)
  have hRref :
      (star (CompactLogTest.laplaceAt (realPartTest g) (-star (s : ℂ)))).im = 0 := by
    have h := laplaceAt_star (realPartTest g) hrealR (-star (s : ℂ))
    rw [h]
    simpa [Complex.star_def] using hRneg
  have hIref :
      (star (CompactLogTest.laplaceAt (imagPartTest g) (-star (s : ℂ)))).im = 0 := by
    have h := laplaceAt_star (imagPartTest g) hrealI (-star (s : ℂ))
    rw [h]
    simpa [Complex.star_def] using hIneg
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    hRref, hIref, hRpos, hIpos]
  ring

/-- The real part of the convolution-square Laplace value splits into the two
component squares at every real spectral point; the cross term contributes no
real part there. -/
theorem laplaceAt_convolutionSquare_re_split_at_real
    (g : CompactLogTest) (s : ℝ) :
    (CompactLogTest.laplaceAt g.convolutionSquare (s : ℂ)).re =
      (CompactLogTest.laplaceAt (realPartTest g).convolutionSquare (s : ℂ)).re +
        (CompactLogTest.laplaceAt (imagPartTest g).convolutionSquare (s : ℂ)).re := by
  rw [laplaceAt_convolutionSquare_eq_componentSquares_add_cross]
  rw [Complex.add_re, Complex.add_re]
  rw [laplaceAt_convolutionSquare_cross_re_zero_at_real]
  simp

/-- The pole endpoint only samples real spectral points, so its square value
splits exactly into the real and imaginary component squares. -/
theorem poleTerm_convolutionSquare_split (g : CompactLogTest) :
    C1SameOwnerWeil.poleTerm g.convolutionSquare =
      C1SameOwnerWeil.poleTerm (realPartTest g).convolutionSquare +
        C1SameOwnerWeil.poleTerm (imagPartTest g).convolutionSquare := by
  unfold C1SameOwnerWeil.poleTerm
  simp only [Complex.add_re]
  have hplus := laplaceAt_convolutionSquare_re_split_at_real g (1 / 2 : ℝ)
  have hminus := laplaceAt_convolutionSquare_re_split_at_real g (-(1 / 2) : ℝ)
  have hplus' :
      (CompactLogTest.laplaceAt g.convolutionSquare (1 / 2 : ℂ)).re =
        (CompactLogTest.laplaceAt (realPartTest g).convolutionSquare (1 / 2 : ℂ)).re +
          (CompactLogTest.laplaceAt (imagPartTest g).convolutionSquare (1 / 2 : ℂ)).re := by
    convert hplus using 1 <;> norm_num
  have hminus' :
      (CompactLogTest.laplaceAt g.convolutionSquare (-1 / 2 : ℂ)).re =
        (CompactLogTest.laplaceAt (realPartTest g).convolutionSquare (-1 / 2 : ℂ)).re +
          (CompactLogTest.laplaceAt (imagPartTest g).convolutionSquare (-1 / 2 : ℂ)).re := by
    convert hminus using 1 <;> norm_num
  rw [hplus', hminus']
  ring

/-- Each individual finite prime-power coefficient is real-linear in the
convolution-square real part.  This pointwise identity does not yet split the
carrier-trimmed `finitePrimeSum`, whose support is defined by total-term
nonvanishing. -/
theorem finitePrimeTerm_convolutionSquare_re_split
    (g : CompactLogTest) (n : ℕ) :
    C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n =
      C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n +
        C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n := by
  unfold C1SameOwnerWeil.finitePrimeTerm C1SameOwnerWeil.finitePrimeTermComplex
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [convolutionSquare_re_split g (Real.log n),
    convolutionSquare_re_split g (-Real.log n)]
  ring

/-- The exact finite carrier correction needed when the total prime-power
support does not coincide with the component supports. -/
noncomputable def finitePrimeCarrierCorrection (g : CompactLogTest) : Real :=
  let U := C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare ∪
    C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare ∪
    C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare
  Finset.sum U (fun n =>
    (if n ∈ C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare then
        C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n else 0) -
      (if n ∈ C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare then
        C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n else 0) -
      (if n ∈ C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare then
        C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n else 0))

/-- Exact carrier-corrected decomposition of the finite prime-power owner. -/
theorem finitePrimeSum_convolutionSquare_eq_componentSums_add_correction
    (g : CompactLogTest) :
    C1SameOwnerWeil.finitePrimeSum g.convolutionSquare =
      C1SameOwnerWeil.finitePrimeSum (realPartTest g).convolutionSquare +
        C1SameOwnerWeil.finitePrimeSum (imagPartTest g).convolutionSquare +
          finitePrimeCarrierCorrection g := by
  classical
  let T := C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare
  let R := C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare
  let I := C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare
  let U := T ∪ R ∪ I
  have hTU : T ⊆ U := by
    intro n hn
    simp [U, hn]
  have hRU : R ⊆ U := by
    intro n hn
    simp [U, hn]
  have hIU : I ⊆ U := by
    intro n hn
    simp [U, hn]
  have hzero_of_not_mem : ∀ (F : CompactLogTest) {n : ℕ},
      n ∉ C1SameOwnerWeil.globalPrimeIndexSet F →
        C1SameOwnerWeil.finitePrimeTerm F n = 0 := by
    intro F n hn
    have hcomplex : C1SameOwnerWeil.finitePrimeTermComplex F n = 0 := by
      by_contra hne
      apply hn
      exact (C1SameOwnerWeil.mem_globalPrimeIndexSet_iff F n).2
        ⟨C1SameOwnerWeil.finitePrimeTermComplex_nonzero_primePower F hne, hne⟩
    simpa [C1SameOwnerWeil.finitePrimeTerm] using congrArg Complex.re hcomplex
  have hT :
      (Finset.sum U (fun n =>
        if n ∈ T then C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n else 0)) =
        Finset.sum T (fun n => C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n) := by
    calc
      Finset.sum U (fun n =>
          if n ∈ T then C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n else 0) =
          Finset.sum U (fun n => C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n) := by
            apply Finset.sum_congr rfl
            intro n hnU
            by_cases hnT : n ∈ T
            · simp [hnT]
            · have hz := hzero_of_not_mem (g.convolutionSquare) (by simpa [T] using hnT)
              simp [hnT, hz]
      _ = Finset.sum T (fun n => C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n) := by
        symm
        apply Finset.sum_subset hTU
        intro n _hnU hnT
        exact hzero_of_not_mem (g.convolutionSquare) (by simpa [T] using hnT)
  have hR :
      (Finset.sum U (fun n =>
        if n ∈ R then
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n else 0)) =
        Finset.sum R (fun n =>
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n) := by
    calc
      Finset.sum U (fun n =>
          if n ∈ R then
            C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n else 0) =
          Finset.sum U (fun n =>
            C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n) := by
            apply Finset.sum_congr rfl
            intro n hnU
            by_cases hnR : n ∈ R
            · simp [hnR]
            · have hz := hzero_of_not_mem (realPartTest g).convolutionSquare
                (by simpa [R] using hnR)
              simp [hnR, hz]
      _ = Finset.sum R (fun n =>
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n) := by
        symm
        apply Finset.sum_subset hRU
        intro n _hnU hnR
        exact hzero_of_not_mem (realPartTest g).convolutionSquare (by simpa [R] using hnR)
  have hI :
      (Finset.sum U (fun n =>
        if n ∈ I then
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n else 0)) =
        Finset.sum I (fun n =>
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n) := by
    calc
      Finset.sum U (fun n =>
          if n ∈ I then
            C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n else 0) =
          Finset.sum U (fun n =>
            C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n) := by
            apply Finset.sum_congr rfl
            intro n hnU
            by_cases hnI : n ∈ I
            · simp [hnI]
            · have hz := hzero_of_not_mem (imagPartTest g).convolutionSquare
                (by simpa [I] using hnI)
              simp [hnI, hz]
      _ = Finset.sum I (fun n =>
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n) := by
        symm
        apply Finset.sum_subset hIU
        intro n _hnU hnI
        exact hzero_of_not_mem (imagPartTest g).convolutionSquare (by simpa [I] using hnI)
  unfold C1SameOwnerWeil.finitePrimeSum finitePrimeCarrierCorrection
  change Finset.sum T (fun n => C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n) =
    (Finset.sum R (fun n =>
      C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n)) +
      Finset.sum I (fun n =>
        C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n) +
        Finset.sum U (fun n =>
          ((if n ∈ T then C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n else 0) -
            (if n ∈ R then
              C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n else 0) -
            (if n ∈ I then
              C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n else 0))
        )
  rw [← hT, ← hR, ← hI]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- The finite-carrier correction enters the Weil quadratic value with the
opposite sign because `qw` subtracts the finite prime-power owner. -/
theorem qw_convolutionSquare_eq_componentQws_sub_correction
    (g : CompactLogTest) :
    C1SameOwnerWeil.qw g =
      C1SameOwnerWeil.qw (realPartTest g) +
        C1SameOwnerWeil.qw (imagPartTest g) -
          finitePrimeCarrierCorrection g := by
  unfold C1SameOwnerWeil.qw C1SameOwnerWeil.psi
  rw [poleTerm_convolutionSquare_split,
    C1XiCenterTwoGammaComplexSplit.archimedeanTerm_split,
    finitePrimeSum_convolutionSquare_eq_componentSums_add_correction]
  ring

/-- If the trimmed prime-power carrier of a complex square is exactly the
disjoint union of the carriers of its real and imaginary component squares,
then the finite prime sum inherits the pointwise coefficient split.  The
carrier hypothesis is intentionally explicit: total-term cancellation can
otherwise change membership and invalidate a naive sum decomposition. -/
theorem finitePrimeSum_convolutionSquare_split_of_disjoint_carriers
    (g : CompactLogTest)
    (hcarrier :
      C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare =
        C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare ∪
          C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare)
    (hdisjoint :
      Disjoint
        (C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare)
        (C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare)) :
    C1SameOwnerWeil.finitePrimeSum g.convolutionSquare =
      C1SameOwnerWeil.finitePrimeSum (realPartTest g).convolutionSquare +
        C1SameOwnerWeil.finitePrimeSum (imagPartTest g).convolutionSquare := by
  unfold C1SameOwnerWeil.finitePrimeSum
  rw [hcarrier, Finset.sum_union hdisjoint]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hnI : n ∉
        C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare := by
      exact Finset.disjoint_left.1 hdisjoint hn
    have hzero :
        C1SameOwnerWeil.finitePrimeTermComplex
            (imagPartTest g).convolutionSquare n = 0 := by
      by_contra hne
      apply hnI
      exact (C1SameOwnerWeil.mem_globalPrimeIndexSet_iff
        ((imagPartTest g).convolutionSquare) n).2
        ⟨C1SameOwnerWeil.finitePrimeTermComplex_nonzero_primePower
          ((imagPartTest g).convolutionSquare) hne, hne⟩
    have himag :
        C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n = 0 := by
      simpa [C1SameOwnerWeil.finitePrimeTerm] using congrArg Complex.re hzero
    rw [finitePrimeTerm_convolutionSquare_re_split g n, himag, add_zero]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnR : n ∉
        C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare := by
      exact Finset.disjoint_right.1 hdisjoint hn
    have hzero :
        C1SameOwnerWeil.finitePrimeTermComplex
            (realPartTest g).convolutionSquare n = 0 := by
      by_contra hne
      apply hnR
      exact (C1SameOwnerWeil.mem_globalPrimeIndexSet_iff
        ((realPartTest g).convolutionSquare) n).2
        ⟨C1SameOwnerWeil.finitePrimeTermComplex_nonzero_primePower
          ((realPartTest g).convolutionSquare) hne, hne⟩
    have hreal :
        C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n = 0 := by
      simpa [C1SameOwnerWeil.finitePrimeTerm] using congrArg Complex.re hzero
    rw [finitePrimeTerm_convolutionSquare_re_split g n, hreal, zero_add]

/-- Under the explicit carrier-stability hypothesis, the complete same-owner
Weil quadratic value splits into the two real component values.  This is a
conditional complexification lemma, not a proof that the carrier hypothesis
holds for arbitrary tests. -/
theorem qw_split_of_disjoint_component_carriers
    (g : CompactLogTest)
    (hcarrier :
      C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare =
        C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare ∪
          C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare)
    (hdisjoint :
      Disjoint
        (C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare)
        (C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare)) :
    C1SameOwnerWeil.qw g =
      C1SameOwnerWeil.qw (realPartTest g) +
        C1SameOwnerWeil.qw (imagPartTest g) := by
  unfold C1SameOwnerWeil.qw C1SameOwnerWeil.psi
  rw [poleTerm_convolutionSquare_split,
    C1XiCenterTwoGammaComplexSplit.archimedeanTerm_split,
    finitePrimeSum_convolutionSquare_split_of_disjoint_carriers
      g hcarrier hdisjoint]
  ring

/-- Under carrier stability, the correction is exactly zero.  This records
why the earlier disjoint-carrier split is a special case of the general
carrier-corrected identity. -/
theorem finitePrimeCarrierCorrection_eq_zero_of_disjoint_carriers
    (g : CompactLogTest)
    (hcarrier :
      C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare =
        C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare ∪
          C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare)
    (hdisjoint :
      Disjoint
        (C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare)
        (C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare)) :
    finitePrimeCarrierCorrection g = 0 := by
  have hsum := finitePrimeSum_convolutionSquare_eq_componentSums_add_correction g
  rw [finitePrimeSum_convolutionSquare_split_of_disjoint_carriers
    g hcarrier hdisjoint] at hsum
  linarith

/-! ### The carrier correction is an exact zero, without carrier hypotheses -/

/-- The carrier correction vanishes pointwise for every complex test.

The carrier predicates are trimmed using the complex prime-power term, while
the scalar summands use its real part.  The already-proved identity
`finitePrimeTerm_convolutionSquare_re_split` and the fact that a term outside
its carrier is zero therefore make each summand of the correction zero.  No
disjointness or union hypothesis is needed. -/
theorem finitePrimeCarrierCorrection_eq_zero (g : CompactLogTest) :
    finitePrimeCarrierCorrection g = 0 := by
  classical
  let T := C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare
  let R := C1SameOwnerWeil.globalPrimeIndexSet (realPartTest g).convolutionSquare
  let I := C1SameOwnerWeil.globalPrimeIndexSet (imagPartTest g).convolutionSquare
  let U := T ∪ R ∪ I
  have hzero_of_not_mem : ∀ (F : CompactLogTest) {n : ℕ},
      n ∉ C1SameOwnerWeil.globalPrimeIndexSet F →
        C1SameOwnerWeil.finitePrimeTerm F n = 0 := by
    intro F n hn
    have hcomplex : C1SameOwnerWeil.finitePrimeTermComplex F n = 0 := by
      by_contra hne
      apply hn
      exact (C1SameOwnerWeil.mem_globalPrimeIndexSet_iff F n).2
        ⟨C1SameOwnerWeil.finitePrimeTermComplex_nonzero_primePower F hne, hne⟩
    simpa [C1SameOwnerWeil.finitePrimeTerm] using congrArg Complex.re hcomplex
  unfold finitePrimeCarrierCorrection
  change Finset.sum U (fun n =>
    ((if n ∈ T then C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n else 0) -
      (if n ∈ R then
        C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n else 0) -
      (if n ∈ I then
        C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n else 0))) = 0
  apply Finset.sum_eq_zero
  intro n hnU
  by_cases hnT : n ∈ T
  · by_cases hnR : n ∈ R
    · by_cases hnI : n ∈ I
      · rw [if_pos hnT, if_pos hnR, if_pos hnI,
          finitePrimeTerm_convolutionSquare_re_split g n]
        ring
      · have hI0 :
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (imagPartTest g).convolutionSquare (by simpa [I] using hnI)
        rw [if_pos hnT, if_pos hnR, if_neg hnI,
          finitePrimeTerm_convolutionSquare_re_split g n, hI0]
        ring
    · by_cases hnI : n ∈ I
      · have hR0 :
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (realPartTest g).convolutionSquare (by simpa [R] using hnR)
        rw [if_pos hnT, if_neg hnR, if_pos hnI,
          finitePrimeTerm_convolutionSquare_re_split g n, hR0]
        ring
      · have hR0 :
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (realPartTest g).convolutionSquare (by simpa [R] using hnR)
        have hI0 :
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (imagPartTest g).convolutionSquare (by simpa [I] using hnI)
        rw [if_pos hnT, if_neg hnR, if_neg hnI,
          finitePrimeTerm_convolutionSquare_re_split g n, hR0, hI0]
        ring
  · have hT0 : C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n = 0 :=
      hzero_of_not_mem g.convolutionSquare (by simpa [T] using hnT)
    have hcomponent :
        C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n +
            C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n = 0 := by
      calc
        C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n +
              C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n =
            C1SameOwnerWeil.finitePrimeTerm g.convolutionSquare n :=
          (finitePrimeTerm_convolutionSquare_re_split g n).symm
        _ = 0 := hT0
    by_cases hnR : n ∈ R
    · by_cases hnI : n ∈ I
      · rw [if_neg hnT, if_pos hnR, if_pos hnI]
        linarith
      · have hI0 :
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (imagPartTest g).convolutionSquare (by simpa [I] using hnI)
        rw [if_neg hnT, if_pos hnR, if_neg hnI]
        linarith
    · by_cases hnI : n ∈ I
      · have hR0 :
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (realPartTest g).convolutionSquare (by simpa [R] using hnR)
        rw [if_neg hnT, if_neg hnR, if_pos hnI]
        linarith
      · have hR0 :
          C1SameOwnerWeil.finitePrimeTerm (realPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (realPartTest g).convolutionSquare (by simpa [R] using hnR)
        have hI0 :
          C1SameOwnerWeil.finitePrimeTerm (imagPartTest g).convolutionSquare n = 0 :=
          hzero_of_not_mem (imagPartTest g).convolutionSquare (by simpa [I] using hnI)
        rw [if_neg hnT, if_neg hnR, if_neg hnI]
        linarith

/-- The complete finite prime-power sum splits into the two real component
owners for every complex test. -/
theorem finitePrimeSum_convolutionSquare_eq_componentSums (g : CompactLogTest) :
    C1SameOwnerWeil.finitePrimeSum g.convolutionSquare =
      C1SameOwnerWeil.finitePrimeSum (realPartTest g).convolutionSquare +
        C1SameOwnerWeil.finitePrimeSum (imagPartTest g).convolutionSquare := by
  have hsum := finitePrimeSum_convolutionSquare_eq_componentSums_add_correction g
  rw [finitePrimeCarrierCorrection_eq_zero] at hsum
  simpa using hsum

/-- The complete Weil quadratic value splits into the two real component
values for every complex test. -/
theorem qw_convolutionSquare_eq_componentQws (g : CompactLogTest) :
    C1SameOwnerWeil.qw g =
      C1SameOwnerWeil.qw (realPartTest g) +
        C1SameOwnerWeil.qw (imagPartTest g) := by
  rw [qw_convolutionSquare_eq_componentQws_sub_correction,
    finitePrimeCarrierCorrection_eq_zero, sub_zero]

/-- **Complex-to-real reduction of the W4b sign problem.**

If the Weil quadratic value is nonnegative on every *real* vanishing test,
then it is nonnegative on every complex vanishing test: the exact component
split `qw_convolutionSquare_eq_componentQws` writes the complex value as the
sum of the two component values, each component is a real test
(`isRealTest_realPartTest`, `isRealTest_imagPartTest`), and each component
inherits the vanishing condition
(`realPartTest_vanishesOn_of_vanishesOn`,
`imagPartTest_vanishesOn_of_vanishesOn`).

This is unconditional bookkeeping, not a positivity proof: the remaining W4b
obligation is the sign bound on real tests, now known to suffice for all
tests. -/
theorem qw_nonneg_of_forall_real_vanishing
    {F : Finset CriticalVanishingPoint}
    (hreal : ∀ h : CompactLogTest, IsRealTest h →
      CC20VanishesOn C1.healthyCC20TestSpace F h → 0 ≤ C1SameOwnerWeil.qw h)
    (g : CompactLogTest)
    (hg : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_convolutionSquare_eq_componentQws]
  exact add_nonneg
    (hreal (realPartTest g) (isRealTest_realPartTest g)
      (realPartTest_vanishesOn_of_vanishesOn g hg))
    (hreal (imagPartTest g) (isRealTest_imagPartTest g)
      (imagPartTest_vanishesOn_of_vanishesOn g hg))

/-- The Hermitian square law of a real test collapses: the conjugation leg
disappears and the off-line pair product is the plain product of the two
reflected evaluations. -/
theorem laplaceAt_convolutionSquare_of_isReal
    (g : CompactLogTest) (hreal : IsRealTest g) (s : ℂ) :
    CompactLogTest.laplaceAt g.convolutionSquare s =
      CompactLogTest.laplaceAt g (-s) * CompactLogTest.laplaceAt g s := by
  rw [C1HealthyYoshidaDetector.laplaceAt_convolutionSquare,
    laplaceAt_star g hreal (-star s)]
  congr 1
  rw [star_neg, star_star]

/-- The spectral term of a real test's square is the multiplicity weight
times the explicit reflected product - the phase-route object. -/
theorem spectralTerm_convolutionSquare_of_isReal
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) :
    spectralTerm g.convolutionSquare rho =
      (xiMultiplicity rho : ℂ) *
        (CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho)) *
          CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) := by
  rw [spectralTerm, laplaceAt_convolutionSquare_of_isReal g hreal]

/-- The real part of a real-test spectral term is exactly the multiplicity
weight times the phase-sensitive real part of the reflected product. -/
theorem spectralTerm_convolutionSquare_re_of_isReal
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) :
    (spectralTerm g.convolutionSquare rho).re =
      (xiMultiplicity rho : ℝ) *
        (CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho)) *
          CompactLogTest.laplaceAt g (centeredXiCoordinate rho)).re := by
  rw [spectralTerm_convolutionSquare_of_isReal g hreal rho]
  simp only [Complex.mul_re]
  have hmre : ((xiMultiplicity rho : ℂ).re) = (xiMultiplicity rho : ℝ) := by
    norm_num
  have hmim : ((xiMultiplicity rho : ℂ).im) = 0 := by
    norm_num
  rw [hmre, hmim]
  ring

/-- On the critical line, a real test identifies the reflected transform value
with the conjugate of the original value. -/
theorem laplaceAt_neg_centered_of_isReal_of_onLine
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) (honline : rho.1.re = 1 / 2) :
    CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho)) =
      star (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) := by
  have hcoord := centeredXiCoordinate_star_eq_neg_of_onLine rho honline
  have hstar := laplaceAt_star g hreal (centeredXiCoordinate rho)
  rw [hcoord] at hstar
  exact hstar.symm

/-- The real-test square value at an on-line zero is the norm square of the
single transform value. -/
theorem laplaceAt_convolutionSquare_of_isReal_of_onLine
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) (honline : rho.1.re = 1 / 2) :
    CompactLogTest.laplaceAt g.convolutionSquare
        (centeredXiCoordinate rho) =
      ((Complex.normSq
        (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) : ℝ) : ℂ) := by
  rw [laplaceAt_convolutionSquare_of_isReal g hreal,
    laplaceAt_neg_centered_of_isReal_of_onLine g hreal rho honline,
    Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]

/-- The corresponding on-line spectral term has the expected real norm-square
form, with the natural multiplicity as a real scalar. -/
theorem spectralTerm_convolutionSquare_re_of_isReal_of_onLine
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) (honline : rho.1.re = 1 / 2) :
    (spectralTerm g.convolutionSquare rho).re =
      (xiMultiplicity rho : ℝ) *
        Complex.normSq (CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) := by
  rw [spectralTerm, laplaceAt_convolutionSquare_of_isReal_of_onLine
    g hreal rho honline]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]

/-- For a real test, the Hermitian partner turns the reflected product into its
complex conjugate.  This is the phase-level counterpart of the generic W4a
partner transport. -/
theorem laplaceAt_hermitianPartner_product_eq_star_of_isReal
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) :
    CompactLogTest.laplaceAt g (-(centeredXiCoordinate (hermitianPartner rho))) *
        CompactLogTest.laplaceAt g (centeredXiCoordinate (hermitianPartner rho)) =
      star (CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho)) *
        CompactLogTest.laplaceAt g (centeredXiCoordinate rho)) := by
  rw [centeredXiCoordinate_hermitianPartner]
  have hright := (laplaceAt_star g hreal (centeredXiCoordinate rho)).symm
  have hleft := (laplaceAt_star g hreal (-(centeredXiCoordinate rho))).symm
  have hleft' :
      CompactLogTest.laplaceAt g (-star (centeredXiCoordinate rho)) =
        star (CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho))) := by
    simpa using hleft
  rw [show -(-star (centeredXiCoordinate rho)) = star (centeredXiCoordinate rho) by ring,
    hright, hleft']
  exact (star_mul
    (CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho)))
    (CompactLogTest.laplaceAt g (centeredXiCoordinate rho))).symm

/-! ### Right-half phase readback -/

/-- The multiplicity-weighted phase kernel carried by one right-half zero. -/
def rightHalfPhaseKernel (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) : ℝ :=
  (xiMultiplicity rho : ℝ) *
    (CompactLogTest.laplaceAt g (-(centeredXiCoordinate rho)) *
      CompactLogTest.laplaceAt g (centeredXiCoordinate rho)).re

/-- The real part of one right-half indicator term reads back to the explicit
phase kernel exposed by the real-test square law.  The indicator is kept on
the whole zero index type, matching the W4b pairing ledger. -/
theorem rightHalfSpectralTerm_re_eq_indicator_phase
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) :
    (Set.indicator rightHalfOffLine
        (spectralTerm g.convolutionSquare) rho).re =
      Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho := by
  by_cases h : rho ∈ rightHalfOffLine
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simpa [rightHalfPhaseKernel] using
      spectralTerm_convolutionSquare_re_of_isReal g hreal rho
  · simp [h]

/-- Mechanical tsum-level readback of the right-half residual: for a real
test, its real part is the tsum of multiplicity-weighted phase kernels over
the right-half indicator.  This is an identity only; the missing W4b bound is
still a separate inequality about this real series. -/
theorem rightHalfSpectralSum_re_eq_tsum_indicator_phase
    (g : CompactLogTest) (hreal : IsRealTest g) :
    (rightHalfSpectralSum g).re =
      ∑' rho : sourceNontrivialZeroSet,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho := by
  have hsum := summable_rightHalfSpectralTerm g
  unfold rightHalfSpectralSum
  rw [Complex.re_tsum hsum]
  exact tsum_congr fun rho =>
    rightHalfSpectralTerm_re_eq_indicator_phase g hreal rho

/-- The remaining W4b inequality restricted to the pointwise-real,
F-vanishing subspace, expressed directly in terms of the named phase kernel.
This is a proposition-valued target, not an assumed axiom or positivity fact.
The unrestricted `CompactLogTest` target in `C1SpectralQwAssembly` remains
strictly stronger. -/
def rightHalfPhaseBound_onRealVanishing
    {F : Finset CriticalVanishingPoint} : Prop :=
  ∀ g : CompactLogTest, IsRealTest g →
    CC20VanishesOn C1.healthyCC20TestSpace F g →
      (∑' rho : sourceNontrivialZeroSet,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ≥
        -(1 / 2 : ℝ) * onLineSpectralMass g

/-- On real tests, the phase-kernel target is exactly the original right-half
spectral-sum target; the theorem is only a change of presentation. -/
theorem rightHalfPhaseBound_onRealVanishing_iff_spectral
    {F : Finset CriticalVanishingPoint} :
    rightHalfPhaseBound_onRealVanishing (F := F) ↔
      (∀ g : CompactLogTest, IsRealTest g →
        CC20VanishesOn C1.healthyCC20TestSpace F g →
          (rightHalfSpectralSum g).re ≥
            -(1 / 2 : ℝ) * onLineSpectralMass g) := by
  unfold rightHalfPhaseBound_onRealVanishing
  constructor
  · intro h g hreal hvanishes
    rw [rightHalfSpectralSum_re_eq_tsum_indicator_phase g hreal]
    exact h g hreal hvanishes
  · intro h g hreal hvanishes
    have hspectral := h g hreal hvanishes
    rw [rightHalfSpectralSum_re_eq_tsum_indicator_phase g hreal] at hspectral
    exact hspectral

/-! ### Finite-prefix and tail bookkeeping for the phase series -/

/-- The real phase terms inherit summability from the already-proved complex
right-half spectral series.  This is a convergence statement only; it does not
control the sign of any phase term or of their total. -/
theorem summable_rightHalfPhaseTerm
    (g : CompactLogTest) (hreal : IsRealTest g) :
    Summable (fun rho : sourceNontrivialZeroSet =>
      Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) := by
  have hsumRe : Summable (fun rho : sourceNontrivialZeroSet =>
      (Set.indicator rightHalfOffLine
        (spectralTerm g.convolutionSquare) rho).re) :=
    RCLike.reCLM.summable (summable_rightHalfSpectralTerm g)
  exact hsumRe.congr fun rho =>
    rightHalfSpectralTerm_re_eq_indicator_phase g hreal rho

/-- Exact decomposition of the total phase tsum into a finite prefix and the
complementary subtype tail.  The finite set is arbitrary and is therefore a
reusable interface for later analytic estimates. -/
theorem rightHalfPhaseTsum_eq_prefix_add_tail
    (g : CompactLogTest) (hreal : IsRealTest g)
    (T : Finset sourceNontrivialZeroSet) :
    (∑' rho : sourceNontrivialZeroSet,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) =
      (∑ rho ∈ T,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) +
        ∑' rho : {rho // rho ∉ T},
          Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho := by
  exact (Summable.sum_add_tsum_subtype_compl
    (summable_rightHalfPhaseTerm g hreal) T).symm

/-- A termwise scalar majorant for the phase kernel.  It is the real-part
contraction `|Re z| ≤ ‖z‖` followed by the existing spectral norm readback. -/
theorem rightHalfPhaseTerm_norm_le_spectralNormTerm
    (g : CompactLogTest) (hreal : IsRealTest g)
    (rho : sourceNontrivialZeroSet) :
    ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ ≤
      Set.indicator rightHalfOffLine
        (spectralNormTerm g.convolutionSquare) rho := by
  by_cases h : rho ∈ rightHalfOffLine
  · have hphase := rightHalfSpectralTerm_re_eq_indicator_phase g hreal rho
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h] at hphase
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ← hphase]
    simpa only [Real.norm_eq_abs, norm_spectralTerm] using
      (Complex.abs_re_le_norm (spectralTerm g.convolutionSquare rho))
  · simp [h]

/-- The phase-term norm series is summable by comparison with the existing
scalar spectral majorant.  Keeping this proof named lets later tail and
cofinality lemmas reuse the same absolute-convergence witness. -/
theorem summable_rightHalfPhaseNorm
    (g : CompactLogTest) (hreal : IsRealTest g) :
    Summable (fun rho : sourceNontrivialZeroSet =>
      ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) := by
  have hmajorant : Summable (fun rho : sourceNontrivialZeroSet =>
      Set.indicator rightHalfOffLine
        (spectralNormTerm g.convolutionSquare) rho) :=
    (summable_spectralNormTerm g.convolutionSquare).indicator rightHalfOffLine
  exact Summable.of_nonneg_of_le
    (fun rho => norm_nonneg _)
    (fun rho => rightHalfPhaseTerm_norm_le_spectralNormTerm g hreal rho)
    hmajorant

/-- The complement tail is bounded in norm by the tsum of its termwise norms.
This is the explicit, auditable error budget that remains after selecting a
finite zero prefix. -/
theorem rightHalfPhaseTail_norm_le_tsum_norm
    (g : CompactLogTest) (hreal : IsRealTest g)
    (T : Finset sourceNontrivialZeroSet) :
    ‖∑' rho : {rho // rho ∉ T},
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ ≤
    ∑' rho : {rho // rho ∉ T},
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ := by
  exact norm_tsum_le_tsum_norm
    ((summable_rightHalfPhaseNorm g hreal).subtype
      (fun rho => rho ∉ T))

/-- Absolute phase tails can be made arbitrarily small by enlarging a finite
prefix.  This is the cofinality consequence of unconditional summability; it
does not provide the missing phase lower bound. -/
theorem exists_rightHalfPhasePrefix_tail_budget_lt
    (g : CompactLogTest) (hreal : IsRealTest g)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ T : Finset sourceNontrivialZeroSet,
      (∑' rho : {rho // rho ∉ T},
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) < epsilon := by
  have hEventually : ∀ᶠ T : Finset sourceNontrivialZeroSet in atTop,
      (∑' rho : {rho // rho ∉ T},
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) < epsilon :=
    (tendsto_order.1 (tendsto_tsum_compl_atTop_zero
      (fun rho : sourceNontrivialZeroSet =>
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖))).2
      epsilon hepsilon
  rcases (eventually_atTop.1 hEventually) with ⟨T, hT⟩
  exact ⟨T, hT T le_rfl⟩

/-- The actual complex phase tail inherits the same arbitrarily-small budget.
This is the useful form for combining a finite-prefix phase estimate with the
global W4b target. -/
theorem exists_rightHalfPhasePrefix_phaseTail_norm_lt
    (g : CompactLogTest) (hreal : IsRealTest g)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ T : Finset sourceNontrivialZeroSet,
      ‖∑' rho : {rho // rho ∉ T},
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ < epsilon := by
  obtain ⟨T, hT⟩ := exists_rightHalfPhasePrefix_tail_budget_lt g hreal hepsilon
  exact ⟨T, (rightHalfPhaseTail_norm_le_tsum_norm g hreal T).trans_lt hT⟩

/-- Lower-bound form of the finite-prefix reduction.  Closing W4b now amounts
to proving that the finite prefix minus this explicit tail budget is at least
`-(1/2) * onLineSpectralMass`; this theorem itself is unconditional. -/
theorem rightHalfPhaseTsum_ge_prefix_sub_tailNorm
    (g : CompactLogTest) (hreal : IsRealTest g)
    (T : Finset sourceNontrivialZeroSet) :
    (∑' rho : sourceNontrivialZeroSet,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ≥
      (∑ rho ∈ T,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) -
        ∑' rho : {rho // rho ∉ T},
          ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ := by
  rw [rightHalfPhaseTsum_eq_prefix_add_tail g hreal T]
  have htail := rightHalfPhaseTail_norm_le_tsum_norm g hreal T
  have htailLower : -‖∑' rho : {rho // rho ∉ T},
      Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ ≤
      ∑' rho : {rho // rho ∉ T},
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho := by
    exact neg_le_of_abs_le (by simpa [Real.norm_eq_abs])
  linarith

/-- A finite-prefix certificate closes the phase lower bound.  The certificate
consists of a prefix value above the target by `epsilon` and a complementary
tail norm strictly below the same margin. -/
theorem rightHalfPhaseBound_of_prefix_tail_certificate
    (g : CompactLogTest) (hreal : IsRealTest g)
    (T : Finset sourceNontrivialZeroSet) {epsilon : ℝ}
    (hprefix :
      -(1 / 2 : ℝ) * onLineSpectralMass g + epsilon ≤
        (∑ rho ∈ T,
          Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho))
    (htail :
      (∑' rho : {rho // rho ∉ T},
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) <
        epsilon) :
    (∑' rho : sourceNontrivialZeroSet,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ≥
      -(1 / 2 : ℝ) * onLineSpectralMass g := by
  have hledger := rightHalfPhaseTsum_ge_prefix_sub_tailNorm g hreal T
  have hstrict :
      -(1 / 2 : ℝ) * onLineSpectralMass g <
        (∑ rho ∈ T,
          Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) -
          ∑' rho : {rho // rho ∉ T},
            ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ := by
    linarith
  exact le_of_lt (lt_of_lt_of_le hstrict hledger)

/-- The remaining real-test W4b obligation packaged as a finite-prefix
certificate.  For each pointwise-real F-vanishing test there must exist one
finite zero prefix and one positive margin such that the phase sum over the
prefix beats `-(1/2) * onLineSpectralMass` by at least the margin while the
audited absolute tail of the complementary zeros stays below it.  The margin
is EXISTENTIAL: demanding a fresh certificate for every positive margin would
be too strong, because the absolutely summable phase series bounds every
finite prefix uniformly (see `not_rightHalfPhasePrefix_unboundedMargins`). -/
def rightHalfPhasePrefixCertificate_onRealVanishing
    {F : Finset CriticalVanishingPoint} : Prop :=
  ∀ g : CompactLogTest, IsRealTest g →
    CC20VanishesOn C1.healthyCC20TestSpace F g →
      ∃ margin > (0 : ℝ),
        ∃ T : Finset sourceNontrivialZeroSet,
          -(1 / 2 : ℝ) * onLineSpectralMass g + margin ≤
              (∑ rho ∈ T,
                Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ∧
            (∑' rho : {rho // rho ∉ T},
              ‖Set.indicator rightHalfOffLine
                (rightHalfPhaseKernel g) rho‖) < margin

/-- A prefix certificate is sufficient for the real-test phase target.  This
is an assembly theorem only; producing the certificate is the open analytic
part of W4b. -/
theorem rightHalfPhaseBound_onRealVanishing_of_prefix_certificate
    {F : Finset CriticalVanishingPoint}
    (hcert : rightHalfPhasePrefixCertificate_onRealVanishing (F := F)) :
    rightHalfPhaseBound_onRealVanishing (F := F) := by
  intro g hreal hvanishes
  obtain ⟨margin, _, T, hprefix, htail⟩ := hcert g hreal hvanishes
  exact rightHalfPhaseBound_of_prefix_tail_certificate
    g hreal T hprefix htail

/-! ### The certificate is exactly the strict phase bound -/

/-- A finite prefix whose phase sum beats the target by a positive margin, with
the audited absolute tail below that same margin, is per test equivalent to the
STRICT lower bound for the total phase tsum.  Forward: the exact prefix/tail
split keeps the strictness - the complementary tail cannot absorb the whole
margin because its norm stays below it.  Backward: cofinality shrinks the tail
and the margin is extracted from the strict gap between the total and the
target. -/
theorem rightHalfPhaseStrictBound_iff_prefixCertificate
    (g : CompactLogTest) (hreal : IsRealTest g) :
    (∃ margin > (0 : ℝ),
      ∃ T : Finset sourceNontrivialZeroSet,
        -(1 / 2 : ℝ) * onLineSpectralMass g + margin ≤
          (∑ rho ∈ T,
            Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ∧
          (∑' rho : {rho // rho ∉ T},
            ‖Set.indicator rightHalfOffLine
              (rightHalfPhaseKernel g) rho‖) < margin) ↔
      ((∑' rho : sourceNontrivialZeroSet,
          Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) >
        -(1 / 2 : ℝ) * onLineSpectralMass g) := by
  set Sphase := (∑' rho : sourceNontrivialZeroSet,
      Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) with hSphase
  set Tg := -(1 / 2 : ℝ) * onLineSpectralMass g with hTg
  constructor
  · rintro ⟨margin, _, T, hprefix, htail⟩
    have hsplit := rightHalfPhaseTsum_eq_prefix_add_tail g hreal T
    set ttail := (∑' rho : {rho // rho ∉ T},
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) with httail
    have habsstrict : |ttail| < margin := by
      simpa [Real.norm_eq_abs] using
        (rightHalfPhaseTail_norm_le_tsum_norm g hreal T).trans_lt htail
    have hlow : -margin < ttail := (abs_lt.mp habsstrict).1
    rw [hSphase, hsplit]
    linarith [hprefix, hlow]
  · intro hstrict
    obtain ⟨T, htail⟩ := exists_rightHalfPhasePrefix_tail_budget_lt g hreal
      (epsilon := (Sphase - Tg) / 2)
      (div_pos (sub_pos.mpr hstrict) zero_lt_two)
    have hsplit := rightHalfPhaseTsum_eq_prefix_add_tail g hreal T
    set ttail := (∑' rho : {rho // rho ∉ T},
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) with httail
    set Pfull := (∑ rho ∈ T,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) with hPdef
    have hpre : Pfull = Sphase - ttail := by linarith [hsplit]
    have habstail : |ttail| ≤ (∑' rho : {rho // rho ∉ T},
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) := by
      simpa [Real.norm_eq_abs] using rightHalfPhaseTail_norm_le_tsum_norm g hreal T
    have habsle : ttail ≤ |ttail| := le_abs_self ttail
    have hsup : ttail < (Sphase - Tg) / 2 := by linarith [habsle, habstail, htail]
    have hstrictbound : Pfull > Sphase - (Sphase - Tg) / 2 := by linarith [hpre, hsup]
    refine ⟨(Sphase - Tg) / 2, ?_, T, ?_, htail⟩
    · exact div_pos (sub_pos.mpr hstrict) zero_lt_two
    · linarith [hstrictbound]

/-! ### The certificate is exactly strict Weil positivity -/

/-
The prefix certificate is not an independent source of positivity.  The
previous theorem identifies it with a strict lower bound for the total phase
sum; the W4b ledger then identifies that strict lower bound with
`0 < qw g`.  Keeping this equivalence explicit prevents a later producer from
mistaking the certificate interface for a weaker, purely analytic premise.
-/
theorem rightHalfPhasePrefixCertificate_iff_qw_pos
    (g : CompactLogTest) (hreal : IsRealTest g) :
    (∃ margin > (0 : ℝ),
      ∃ T : Finset sourceNontrivialZeroSet,
        -(1 / 2 : ℝ) * onLineSpectralMass g + margin ≤
          (∑ rho ∈ T,
            Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ∧
        (∑' rho : {rho // rho ∉ T},
          ‖Set.indicator rightHalfOffLine
            (rightHalfPhaseKernel g) rho‖) < margin) ↔
      0 < C1SameOwnerWeil.qw g := by
  rw [rightHalfPhaseStrictBound_iff_prefixCertificate g hreal]
  constructor
  · intro hphase
    rw [qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum]
    rw [rightHalfSpectralSum_re_eq_tsum_indicator_phase g hreal]
    linarith
  · intro hqw
    rw [qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum] at hqw
    rw [rightHalfSpectralSum_re_eq_tsum_indicator_phase g hreal] at hqw
    linarith

/-- Why the certificate margin must be existential rather than demanded for
EVERY positive epsilon: the phase series is absolutely summable, so every
finite prefix is uniformly bounded above by the total absolute mass of the
series; margins growing without bound would force unbounded prefix sums.  This
records the quantifier fix for `rightHalfPhasePrefixCertificate_onRealVanishing`. -/
theorem not_rightHalfPhasePrefix_unboundedMargins
    (g : CompactLogTest) (hreal : IsRealTest g) :
    ¬(∀ ε > (0 : ℝ), ∃ T : Finset sourceNontrivialZeroSet,
      -(1 / 2 : ℝ) * onLineSpectralMass g + ε ≤
        (∑ rho ∈ T,
          Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ∧
        (∑' rho : {rho // rho ∉ T},
          ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) < ε) := by
  set Mabs := (∑' rho : sourceNontrivialZeroSet,
      ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) with hMdef
  have hboundT : ∀ T : Finset sourceNontrivialZeroSet,
      (∑ rho ∈ T, Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho) ≤ Mabs := by
    intro T
    have hsplit := Summable.sum_add_tsum_subtype_compl (summable_rightHalfPhaseNorm g hreal) T
    have htailnn : 0 ≤ ∑' rho : {rho // rho ∉ T},
        ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖ :=
      tsum_nonneg fun _ => norm_nonneg _
    have hpointwise : ∀ ρ ∈ T,
        Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) ρ ≤
          ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) ρ‖ := by
      intro ρ hmem
      simpa using le_abs_self (Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) ρ)
    exact (Finset.sum_le_sum hpointwise).trans (by linarith [hsplit, htailnn])
  intro hH
  rcases le_total Mabs (-(1 / 2 : ℝ) * onLineSpectralMass g) with hMle | hTgle
  · obtain ⟨T, hprefix, _⟩ := hH 1 zero_lt_one
    have hb := hboundT T
    linarith
  · obtain ⟨T, hprefix, _⟩ := hH ((Mabs - (-(1 / 2 : ℝ) * onLineSpectralMass g)) + 1)
      (by linarith [hTgle])
    have hb := hboundT T
    linarith

/-! ### The autocorrelation mass at the origin -/

/-- The origin value of the Hermitian convolution square is a nonnegative real
mass.  This is the exact existing owner theorem, exposed here for the phase
route without introducing a second convolution definition. -/
theorem convolutionSquare_test_zero_is_real_nonnegative
    (g : CompactLogTest) :
    (g.convolutionSquare.test 0).im = 0 ∧
      0 ≤ (g.convolutionSquare.test 0).re := by
  exact ⟨CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_zero_im g,
    CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_zero_re_nonnegative g⟩

/-- The norm of the origin value is exactly the integrated squared norm of the
root test. -/
theorem norm_convolutionSquare_test_zero_eq_integral_normSq
    (g : CompactLogTest) :
    ‖g.convolutionSquare.test 0‖ =
      ∫ x : ℝ, Complex.normSq (g.test x) := by
  rw [CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_zero_eq_integral_normSq]
  have hnonneg : 0 ≤ ∫ x : ℝ, Complex.normSq (g.test x) :=
    integral_nonneg (fun x => Complex.normSq_nonneg (g.test x))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

#print axioms rightHalfSpectralTerm_re_eq_indicator_phase
#print axioms rightHalfSpectralSum_re_eq_tsum_indicator_phase
#print axioms isRealTest_realPartTest
#print axioms isRealTest_imagPartTest
#print axioms realPartTest_vanishesOn_of_vanishesOn
#print axioms imagPartTest_vanishesOn_of_vanishesOn
#print axioms laplaceAt_convolutionSquare_eq_componentSquares_add_cross
#print axioms laplaceAt_im_eq_zero_of_isRealTest_real
#print axioms laplaceAt_convolutionSquare_cross_re_zero_at_real
#print axioms laplaceAt_convolutionSquare_re_split_at_real
#print axioms poleTerm_convolutionSquare_split
#print axioms finitePrimeTerm_convolutionSquare_re_split
#print axioms finitePrimeSum_convolutionSquare_eq_componentSums_add_correction
#print axioms qw_convolutionSquare_eq_componentQws_sub_correction
#print axioms finitePrimeSum_convolutionSquare_split_of_disjoint_carriers
#print axioms qw_split_of_disjoint_component_carriers
#print axioms finitePrimeCarrierCorrection_eq_zero_of_disjoint_carriers
#print axioms finitePrimeCarrierCorrection_eq_zero
#print axioms finitePrimeSum_convolutionSquare_eq_componentSums
#print axioms qw_convolutionSquare_eq_componentQws
#print axioms qw_nonneg_of_forall_real_vanishing
#print axioms rightHalfPhaseBound_onRealVanishing
#print axioms rightHalfPhaseBound_onRealVanishing_iff_spectral
#print axioms summable_rightHalfPhaseTerm
#print axioms rightHalfPhaseTsum_eq_prefix_add_tail
#print axioms rightHalfPhaseTerm_norm_le_spectralNormTerm
#print axioms summable_rightHalfPhaseNorm
#print axioms rightHalfPhaseTail_norm_le_tsum_norm
#print axioms rightHalfPhaseTsum_ge_prefix_sub_tailNorm
#print axioms rightHalfPhaseBound_of_prefix_tail_certificate
#print axioms rightHalfPhasePrefixCertificate_onRealVanishing
#print axioms rightHalfPhaseBound_onRealVanishing_of_prefix_certificate
#print axioms rightHalfPhaseStrictBound_iff_prefixCertificate
#print axioms rightHalfPhasePrefixCertificate_iff_qw_pos
#print axioms not_rightHalfPhasePrefix_unboundedMargins
#print axioms exists_rightHalfPhasePrefix_tail_budget_lt
#print axioms exists_rightHalfPhasePrefix_phaseTail_norm_lt

end
end C1SpectralRealPair
end Source
end ConnesWeilRH
