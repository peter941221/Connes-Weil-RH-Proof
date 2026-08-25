import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1SpectralHermitianPartner
import ConnesWeilRH.Dev.C1SpectralOnlineNonneg

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
  have hmajorant : Summable (fun rho : sourceNontrivialZeroSet =>
      Set.indicator rightHalfOffLine
        (spectralNormTerm g.convolutionSquare) rho) :=
    (summable_spectralNormTerm g.convolutionSquare).indicator rightHalfOffLine
  have hphaseNorm : Summable (fun rho : sourceNontrivialZeroSet =>
      ‖Set.indicator rightHalfOffLine (rightHalfPhaseKernel g) rho‖) :=
    Summable.of_nonneg_of_le
      (fun rho => norm_nonneg _)
      (fun rho => rightHalfPhaseTerm_norm_le_spectralNormTerm g hreal rho)
      hmajorant
  exact norm_tsum_le_tsum_norm
    (hphaseNorm.subtype (fun rho => rho ∉ T))

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
#print axioms rightHalfPhaseBound_onRealVanishing
#print axioms rightHalfPhaseBound_onRealVanishing_iff_spectral
#print axioms summable_rightHalfPhaseTerm
#print axioms rightHalfPhaseTsum_eq_prefix_add_tail
#print axioms rightHalfPhaseTerm_norm_le_spectralNormTerm
#print axioms rightHalfPhaseTail_norm_le_tsum_norm
#print axioms rightHalfPhaseTsum_ge_prefix_sub_tailNorm

end
end C1SpectralRealPair
end Source
end ConnesWeilRH
