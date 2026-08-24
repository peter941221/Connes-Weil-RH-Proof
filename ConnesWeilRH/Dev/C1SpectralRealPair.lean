import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector

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
open MeasureTheory

noncomputable section

/-! ### Real tests: the conjugation leg collapses -/

/-- A compact log test whose point values are fixed by conjugation.  The
numerical witness family of KT-1040a/b/c has this property. -/
def IsRealTest (g : CompactLogTest) : Prop :=
  ∀ x : ℝ, star (g.test x) = g.test x

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

end
end C1SpectralRealPair
end Source
end ConnesWeilRH
