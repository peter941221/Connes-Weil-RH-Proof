import ConnesWeilRH.Dev.M2WidthPlateau
import ConnesWeilRH.Dev.Wall14PlateauBumpHI
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Source.CCM25Concrete.SelectedYoshidaBridge
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# C1HealthyNarrowPlateau - scaled plateau facts for the healthy owner

The explicit Wall14 plateau has a known positive archimedean direction at
width one, but its square is too wide to be prime-free.  This module begins
the separate narrow-width analysis.  It proves the exact convolution-profile
scaling law for the same smooth plateau and the prime-free support budget at
width `1 / 3`.

No finite-node vanishing, detector existence, spectral sign, or RH statement
is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyNarrowPlateau

open MeasureTheory
open Set
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedYoshidaBridge
open CCM25Concrete.SelectedWeilSquare
open CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner
open Dev.M2Width
open Dev.Wall14Plateau

private theorem wideBump_even (w x : Real) :
    wideBump w (-x) = wideBump w x := by
  unfold wideBump
  rw [show -x / w = -(x / w) by ring, bumpEx_even]

private theorem wideBump_hasCompactSupport (w : Real) (wpos : 0 < w) :
    HasCompactSupport (wideBump w) := by
  unfold HasCompactSupport
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (-w)) (b := w))
  · exact isClosed_closure
  · have hsub : Function.support (wideBump w) ⊆ Set.Icc (-w) w := by
      intro x hx
      exact wideBump_mem_Icc w wpos x hx
    simpa [isClosed_Icc.closure_eq] using closure_mono hsub

private theorem wideBump_mul_integrable (w : Real) (wpos : 0 < w) (y : Real) :
    Integrable (fun t : Real => wideBump w t * wideBump w (y - t)) := by
  have hcont : Continuous (fun t : Real => wideBump w t * wideBump w (y - t)) :=
    (wideBump_contDiff w).continuous.mul
      ((wideBump_contDiff w).continuous.comp (by fun_prop))
  have hcomp : HasCompactSupport (fun t : Real =>
      wideBump w t * wideBump w (y - t)) :=
    HasCompactSupport.mul_right (wideBump_hasCompactSupport w wpos)
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- The real convolution profile before its embedding into the compact-log
Hermitian square. -/
noncomputable def wideConvolutionProfile (w y : Real) : Real :=
  ∫ t : Real, wideBump w t * wideBump w (y - t)

/-- The Hermitian square of the real-even scaled plateau is its ordinary real
convolution profile. -/
theorem wideTest_convolutionSquare_eq_real_integral
    (w : Real) (wpos : 0 < w) (y : Real) :
    (wideTest w wpos).convolutionSquare.test y =
      (wideConvolutionProfile w y : Complex) := by
  rw [CCM25Concrete.CompactLogConvolution.CompactLogTest.convolutionSquare_apply]
  calc
    (∫ t : Real, star ((wideTest w wpos).test (-t)) *
        (wideTest w wpos).test (y - t)) =
        ∫ t : Real, ((wideBump w t * wideBump w (y - t) : Real) : Complex) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [wideTest_apply, wideTest_apply, wideBump_even]
      simp
    _ = (wideConvolutionProfile w y : Complex) := by
      unfold wideConvolutionProfile
      exact ContinuousLinearMap.integral_comp_comm (L := Complex.ofRealCLM)
        (wideBump_mul_integrable w wpos y)

/-- Exact dilation law: the width-`w` plateau square has profile
`w * F_1(y / w)`. -/
theorem wideTest_convolutionSquare_re_eq_scaled_bumpF
    (w : Real) (wpos : 0 < w) (y : Real) :
    ((wideTest w wpos).convolutionSquare.test y).re = w * bumpF (y / w) := by
  rw [wideTest_convolutionSquare_eq_real_integral]
  change wideConvolutionProfile w y = w * bumpF (y / w)
  unfold wideConvolutionProfile
  let h : Real -> Real := fun u => bumpReal u * bumpReal (y / w - u)
  have hfun :
      (fun t : Real => wideBump w t * wideBump w (y - t)) =
        fun t : Real => h (t / w) := by
    funext t
    dsimp [h, wideBump, bumpReal]
    congr 1
    ring
  calc
    (∫ t : Real, wideBump w t * wideBump w (y - t)) =
        ∫ t : Real, h (t / w) := by rw [hfun]
    _ = |w| • ∫ u : Real, h u := Measure.integral_comp_div h w
    _ = w * bumpF (y / w) := by
      rw [abs_of_pos wpos]
      change w * (∫ u : Real, h u) = w * bumpF (y / w)
      rw [← bumpF_eq_conv]

/-- The square mass scales by the same positive width factor. -/
theorem wideTest_convolutionSquare_zero_re_eq_scaled_bumpA
    (w : Real) (wpos : 0 < w) :
    ((wideTest w wpos).convolutionSquare.test 0).re = w * bumpA := by
  calc
    ((wideTest w wpos).convolutionSquare.test 0).re = w * bumpF (0 / w) :=
      wideTest_convolutionSquare_re_eq_scaled_bumpF w wpos 0
    _ = w * bumpA := by rw [zero_div, bumpF_zero_eq_bumpA]

/-- The scaled real plateau square has nonnegative real profile. -/
theorem wideTest_convolutionSquare_re_nonnegative
    (w : Real) (wpos : 0 < w) (y : Real) :
    0 <= ((wideTest w wpos).convolutionSquare.test y).re := by
  rw [wideTest_convolutionSquare_re_eq_scaled_bumpF]
  exact mul_nonneg wpos.le (bumpF_nonneg (y / w))

/-- Cauchy--Schwarz controls every scaled profile value by its origin mass. -/
theorem wideTest_convolutionSquare_re_le_zero_mass
    (w : Real) (wpos : 0 < w) (y : Real) :
    ((wideTest w wpos).convolutionSquare.test y).re <=
      ((wideTest w wpos).convolutionSquare.test 0).re := by
  rw [wideTest_convolutionSquare_re_eq_scaled_bumpF,
    wideTest_convolutionSquare_zero_re_eq_scaled_bumpA]
  exact mul_le_mul_of_nonneg_left (bumpF_le_bumpA (y / w)) wpos.le

/-- The scaled profile vanishes outside its doubled support interval. -/
theorem wideTest_convolutionSquare_re_eq_zero_of_two_mul_w_le_abs
    (w : Real) (wpos : 0 < w) (y : Real)
    (hy : 2 * w <= |y|) :
    ((wideTest w wpos).convolutionSquare.test y).re = 0 := by
  rw [wideTest_convolutionSquare_re_eq_scaled_bumpF]
  have hscaled : (2 : Real) <= |y / w| := by
    rw [abs_div, abs_of_pos wpos]
    exact (le_div_iff₀ wpos).mpr hy
  rw [bumpF_eq_zero_of_two_le_abs (y / w) hscaled, mul_zero]

private theorem wideTest_support_subset_open
    (w : Real) (wpos : 0 < w) :
    Function.support (wideTest w wpos).test ⊆ Set.Ioo (-w) w := by
  intro x hx
  have hnonzero : wideBump w x ≠ 0 := by
    intro hzero
    apply hx
    simp [wideTest_apply, hzero]
  exact abs_lt.mp (wideBump_abs_lt w wpos x hnonzero)

/-- The genuine square of a width-`w` plateau is supported in the doubled
open interval. -/
theorem wideTest_convolutionSquare_support_subset_open_double
    (w : Real) (wpos : 0 < w) :
    Function.support (wideTest w wpos).convolutionSquare.test ⊆
      Set.Ioo (-(2 * w)) (2 * w) := by
  have hsquare := convolutionSquare_support_subset_difference
    (wideTest w wpos) (wideTest_support_subset_open w wpos)
  intro x hx
  rcases hsquare hx with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- Width `1 / 3` leaves a strict support gap before the first prime-power
locations at positive and negative `log 2`. -/
noncomputable def primeFreeWidth : Real := 1 / 3

lemma primeFreeWidth_pos : 0 < primeFreeWidth := by
  unfold primeFreeWidth
  norm_num

noncomputable def primeFreePlateau : CompactLogTest :=
  wideTest primeFreeWidth primeFreeWidth_pos

private lemma exp_sub_one_le_six_fifths
    (t : Real) (ht0 : 0 <= t) (ht1 : t <= 1 / 6) :
    Real.exp t - 1 <= (6 / 5 : Real) * t := by
  have h := Real.exp_bound' ht0 (ht1.trans (by norm_num))
    (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  nlinarith [sq_nonneg t]

private lemma exp_two_thirds_gt :
    (37 / 19 : Real) < Real.exp (2 / 3) := by
  have h := Real.exp_bound (x := (2 / 3 : Real))
    (by norm_num : |(2 / 3 : Real)| <= 1) (n := 7) (by norm_num)
  have hlow := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ] at hlow
  nlinarith

theorem primeFreePlateau_square_re_eq_scaled_bumpF (y : Real) :
    (primeFreePlateau.convolutionSquare.test y).re =
      primeFreeWidth * bumpF (y / primeFreeWidth) := by
  change ((wideTest primeFreeWidth primeFreeWidth_pos).convolutionSquare.test y).re = _
  exact wideTest_convolutionSquare_re_eq_scaled_bumpF
    primeFreeWidth primeFreeWidth_pos y

noncomputable def primeFreeArchG (y : Real) : Real :=
  (C1SameOwnerWeil.archimedeanNumerator
    primeFreePlateau.convolutionSquare y).re / den y

theorem primeFreeArchG_eq_formula (y : Real) :
    primeFreeArchG y =
      (2 * primeFreeWidth) *
        (Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA) / den y := by
  unfold primeFreeArchG C1SameOwnerWeil.archimedeanNumerator
  rw [primeFreePlateau.convolutionSquare_add_neg_eq_two_re]
  have h1 :
      (Complex.ofRealCLM (Real.exp (y / 2)) *
          ((2 * (primeFreePlateau.convolutionSquare.test y).re : Real) : Complex)).re =
        Real.exp (y / 2) * (2 * (primeFreePlateau.convolutionSquare.test y).re) := by
    change (((Real.exp (y / 2) : Real) : Complex) *
      ((2 * (primeFreePlateau.convolutionSquare.test y).re : Real) : Complex)).re = _
    rw [Complex.re_ofReal_mul]
    simp
  have h2 :
      ((2 : Complex) * primeFreePlateau.convolutionSquare.test 0).re =
        2 * (primeFreePlateau.convolutionSquare.test 0).re := by
    change (((2 : Real) : Complex) * primeFreePlateau.convolutionSquare.test 0).re = _
    rw [Complex.re_ofReal_mul]
  have hmass :
      (primeFreePlateau.convolutionSquare.test 0).re =
        primeFreeWidth * bumpA := by
    change ((wideTest primeFreeWidth primeFreeWidth_pos).convolutionSquare.test 0).re = _
    exact wideTest_convolutionSquare_zero_re_eq_scaled_bumpA
      primeFreeWidth primeFreeWidth_pos
  rw [Complex.sub_re, h1, h2,
    primeFreePlateau_square_re_eq_scaled_bumpF, hmass]
  unfold primeFreeWidth
  ring_nf

private theorem primeFreeArchG_abs_le_near
    (y : Real) (hy0 : 0 < y) (hyw : y <= primeFreeWidth) :
    |primeFreeArchG y| <= 1 + bumpA / 5 := by
  have hx0 : 0 <= y / primeFreeWidth :=
    div_nonneg hy0.le primeFreeWidth_pos.le
  have hx1 : y / primeFreeWidth <= 1 := by
    exact (div_le_iff₀ primeFreeWidth_pos).mpr (by simpa using hyw)
  have ht0 : 0 <= y / 2 := by positivity
  have ht1 : y / 2 <= (1 / 6 : Real) := by
    unfold primeFreeWidth at hyw
    linarith
  have hE : Real.exp (y / 2) - 1 <= (6 / 5 : Real) * (y / 2) :=
    exp_sub_one_le_six_fifths (y / 2) ht0 ht1
  have hEn : 0 <= Real.exp (y / 2) - 1 := by
    have hone : (1 : Real) <= Real.exp (y / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr ht0
    linarith
  have hF0 : 0 <= bumpF (y / primeFreeWidth) :=
    bumpF_nonneg _
  have hFA : bumpF (y / primeFreeWidth) <= bumpA :=
    bumpF_le_bumpA _
  have hdiff :
      |bumpF (y / primeFreeWidth) - bumpA| <= y / primeFreeWidth := by
    rw [abs_sub_comm]
    exact bumpA_sub_bumpF_le (y / primeFreeWidth) hx0 hx1
  have hsplit :
      |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <=
        (Real.exp (y / 2) - 1) * bumpF (y / primeFreeWidth) +
          |bumpF (y / primeFreeWidth) - bumpA| := by
    have hrewrite :
        Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA =
          bumpF (y / primeFreeWidth) * (Real.exp (y / 2) - 1) +
            (bumpF (y / primeFreeWidth) - bumpA) := by ring
    calc
      |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| =
          |bumpF (y / primeFreeWidth) * (Real.exp (y / 2) - 1) +
            (bumpF (y / primeFreeWidth) - bumpA)| := by rw [hrewrite]
      _ <= |bumpF (y / primeFreeWidth) * (Real.exp (y / 2) - 1)| +
          |bumpF (y / primeFreeWidth) - bumpA| := abs_add_le _ _
      _ = (Real.exp (y / 2) - 1) * bumpF (y / primeFreeWidth) +
          |bumpF (y / primeFreeWidth) - bumpA| := by
        rw [abs_mul, abs_of_nonneg hF0, abs_of_nonneg hEn]
        ring
  have hmain :
      (Real.exp (y / 2) - 1) * bumpF (y / primeFreeWidth) <=
        (6 / 5 : Real) * (y / 2) * bumpA := by
    exact mul_le_mul hE hFA hF0 (by positivity)
  have hnum :
      |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <=
        y * (3 + 3 * bumpA / 5) := by
    have hscale : y / primeFreeWidth = 3 * y := by
      unfold primeFreeWidth
      field_simp
    calc
      |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <=
          (Real.exp (y / 2) - 1) * bumpF (y / primeFreeWidth) +
            |bumpF (y / primeFreeWidth) - bumpA| := hsplit
      _ <= (6 / 5 : Real) * (y / 2) * bumpA + y / primeFreeWidth :=
        add_le_add hmain hdiff
      _ = (6 / 5 : Real) * (y / 2) * bumpA + 3 * y := by rw [hscale]
      _ = y * (3 + 3 * bumpA / 5) := by ring_nf
  have hden : 0 < den y := den_pos y hy0
  have hden_lower : 2 * y <= den y := deny_ge_two y (le_of_lt hy0)
  rw [primeFreeArchG_eq_formula, abs_div, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) primeFreeWidth_pos.le),
    abs_of_pos hden]
  have hscale_nonneg : 0 <= 2 * primeFreeWidth :=
    mul_nonneg (by norm_num) primeFreeWidth_pos.le
  have hq : 0 <= 1 + bumpA / 5 := by
    nlinarith [bumpA_pos]
  have hnum_scaled :
      (2 * primeFreeWidth) *
          |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <=
        (2 * primeFreeWidth) * (y * (3 + 3 * bumpA / 5)) :=
    mul_le_mul_of_nonneg_left hnum hscale_nonneg
  have hden_scaled :
      (1 + bumpA / 5) * (2 * y) <= (1 + bumpA / 5) * den y :=
    mul_le_mul_of_nonneg_left hden_lower hq
  apply (div_le_iff₀ hden).mpr
  calc
    (2 * primeFreeWidth) *
        |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <=
        (2 * primeFreeWidth) * (y * (3 + 3 * bumpA / 5)) := hnum_scaled
    _ = (1 + bumpA / 5) * (2 * y) := by
      unfold primeFreeWidth
      ring
    _ <= (1 + bumpA / 5) * den y := hden_scaled

private theorem primeFreeArchG_abs_le_mid
    (y : Real) (hyw : primeFreeWidth <= y)
    (hy2w : y <= 2 * primeFreeWidth) :
    |primeFreeArchG y| <= primeFreeWidth * bumpA / y := by
  have hy0 : 0 < y := primeFreeWidth_pos.trans_le hyw
  have hx1 : 1 <= y / primeFreeWidth := by
    exact (le_div_iff₀ primeFreeWidth_pos).mpr (by simpa using hyw)
  have hx2 : y / primeFreeWidth <= 2 := by
    exact (div_le_iff₀ primeFreeWidth_pos).mpr hy2w
  have hxy : y <= y / primeFreeWidth := by
    have hwle : primeFreeWidth <= 1 := by
      unfold primeFreeWidth
      norm_num
    exact (le_div_iff₀ primeFreeWidth_pos).mpr (by nlinarith)
  have hF0 : 0 <= bumpF (y / primeFreeWidth) := bumpF_nonneg _
  have hE : Real.exp (y / 2) <= Real.exp ((y / primeFreeWidth) / 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hsmall :
      Real.exp (y / primeFreeWidth / 2) * bumpF (y / primeFreeWidth) <= bumpA :=
    bump_expHalfF_le_A (y / primeFreeWidth) hx1 hx2
  have hupper :
      Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA <= 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hE hF0, hsmall]
  have hlower :
      -bumpA <= Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA := by
    have hEp : 0 <= Real.exp (y / 2) := (Real.exp_pos _).le
    have hprod : 0 <= Real.exp (y / 2) * bumpF (y / primeFreeWidth) :=
      mul_nonneg hEp hF0
    linarith
  have hnum :
      |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <= bumpA :=
    abs_le.mpr ⟨hlower, hupper.trans (le_of_lt bumpA_pos)⟩
  have hden : 0 < den y := den_pos y hy0
  have hden_lower : 2 * y <= den y := deny_ge_two y (le_of_lt hy0)
  rw [primeFreeArchG_eq_formula, abs_div, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) primeFreeWidth_pos.le),
    abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    (2 * primeFreeWidth) *
        |Real.exp (y / 2) * bumpF (y / primeFreeWidth) - bumpA| <=
        (2 * primeFreeWidth) * bumpA :=
      mul_le_mul_of_nonneg_left hnum (mul_nonneg (by norm_num) primeFreeWidth_pos.le)
    _ = (2 * primeFreeWidth * bumpA) := by ring
    _ = (primeFreeWidth * bumpA / y) * (2 * y) := by
      have hyne : y ≠ 0 := ne_of_gt hy0
      field_simp [hyne]
    _ <= (primeFreeWidth * bumpA / y) * den y := by
      exact mul_le_mul_of_nonneg_left hden_lower
        (div_nonneg (mul_nonneg primeFreeWidth_pos.le bumpA_pos.le) hy0.le)

private theorem primeFreeArchG_abs_eq_tail
    (y : Real) (hy2w : 2 * primeFreeWidth <= y) :
    |primeFreeArchG y| = (2 * primeFreeWidth) * bumpA / den y := by
  have hy0 : 0 < y :=
    lt_of_lt_of_le (mul_pos (by norm_num) primeFreeWidth_pos) hy2w
  have hden : 0 < den y := den_pos y hy0
  have hx2 : 2 <= y / primeFreeWidth := by
    exact (le_div_iff₀ primeFreeWidth_pos).mpr hy2w
  have hF : bumpF (y / primeFreeWidth) = 0 := by
    apply bumpF_eq_zero_of_two_le_abs
    simpa [abs_of_nonneg (by linarith : 0 <= y / primeFreeWidth)] using hx2
  rw [primeFreeArchG_eq_formula, hF]
  have hnum :
      Real.exp (y / 2) * 0 - bumpA = -bumpA := by ring
  rw [hnum, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (mul_nonneg (by norm_num) primeFreeWidth_pos.le),
    abs_of_pos hden, abs_of_pos bumpA_pos]

private noncomputable def primeFreeSelectedOwner : SelectedWeilSquareOwner :=
  SelectedWeilSquareOwner.ofCompactLogTest primeFreePlateau

private lemma primeFree_archimedeanIntegrand_eq_of_pos
    (y : Real) (hy : 0 < y) :
    primeFreeSelectedOwner.archimedeanIntegrand y =
      (primeFreeArchG y : Complex) := by
  apply Complex.ext
  · unfold primeFreeSelectedOwner primeFreeArchG
      SelectedWeilSquareOwner.archimedeanIntegrand
    have hd0 : (den y : Complex) ≠ 0 := by
      exact_mod_cast (den_pos y hy).ne'
    have hden_ne : den y ≠ 0 := (den_pos y hy).ne'
    have him :
        ((SelectedWeilSquareOwner.ofCompactLogTest primeFreePlateau).archimedeanNumerator y).im = 0 :=
      (SelectedWeilSquareOwner.ofCompactLogTest primeFreePlateau).archimedeanNumerator_im_eq_zero y
    have hden : archimedeanDenominator y = den y := by rfl
    rw [hden, Complex.div_re]
    have hd : ((den y : Complex)).im = 0 := by simp
    have hr : ((den y : Complex)).re = den y := by simp
    have hnorm : Complex.normSq (den y : Complex) = (den y) ^ 2 := by
      rw [Complex.normSq_apply, hr, hd]
      ring
    rw [him, hr, hd, hnorm]
    simp only [Complex.ofReal_re]
    have hnum :
        ((SelectedWeilSquareOwner.ofCompactLogTest primeFreePlateau).archimedeanNumerator y).re =
          (C1SameOwnerWeil.archimedeanNumerator
            primeFreePlateau.convolutionSquare y).re := by
      rfl
    rw [hnum]
    field_simp [hden_ne]
    ring
  · simp [primeFreeSelectedOwner,
      SelectedWeilSquareOwner.archimedeanIntegrand_im_eq_zero]

private lemma primeFree_archimedeanIntegrand_norm_eq_abs
    (y : Real) (hy : 0 < y) :
    ‖primeFreeSelectedOwner.archimedeanIntegrand y‖ = |primeFreeArchG y| := by
  rw [primeFree_archimedeanIntegrand_eq_of_pos y hy]
  simp

private lemma primeFreeArchG_abs_integrableOn_Ioi :
    IntegrableOn (fun y : Real => |primeFreeArchG y|) (Ioi (0 : Real)) := by
  have hnorm : IntegrableOn
      (fun y : Real => ‖primeFreeSelectedOwner.archimedeanIntegrand y‖)
      (Ioi (0 : Real)) :=
    primeFreeSelectedOwner.archimedeanIntegrand_integrableOn_Ioi.norm
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hnorm
  intro y hy
  have hy0 : 0 < y := by exact hy
  exact (primeFree_archimedeanIntegrand_norm_eq_abs y hy0).symm

private lemma primeFreeArchG_near_integral_le :
    (∫ y in Ioc (0 : Real) primeFreeWidth, |primeFreeArchG y|) <=
      (34 / 135 : Real) * bumpA := by
  let mu : Measure Real := volume.restrict (Ioc (0 : Real) primeFreeWidth)
  let K : Real := 1 + bumpA / 5
  have hmeas : MeasurableSet (Ioc (0 : Real) primeFreeWidth) := measurableSet_Ioc
  have hbnd : (fun y : Real => |primeFreeArchG y|) ≤ᵐ[mu]
      (fun _ : Real => K) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact primeFreeArchG_abs_le_near y hy.1 hy.2
  have hnon : (fun _ : Real => (0 : Real)) ≤ᵐ[mu]
      (fun y : Real => |primeFreeArchG y|) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact abs_nonneg (primeFreeArchG y)
  have hfin : (volume : Measure Real) (Ioc (0 : Real) primeFreeWidth) ≠ ⊤ := by
    simp [Real.volume_Ioc, primeFreeWidth]
  haveI : IsFiniteMeasure mu := MeasureTheory.isFiniteMeasure_restrict.mpr
    (by simpa [mu] using hfin)
  have hKint : Integrable (fun _ : Real => K) mu :=
    MeasureTheory.integrable_const K
  have hsum_eq : (∫ y : Real, K ∂mu) = K * primeFreeWidth := by
    calc
      (∫ y : Real, K ∂mu) = mu.real Set.univ * K := by
        simp [MeasureTheory.integral_const]
      _ = K * primeFreeWidth := by
        have hvol : mu.real Set.univ = primeFreeWidth := by
          change (mu Set.univ).toReal = primeFreeWidth
          simp [mu, Real.volume_Ioc, primeFreeWidth]
        rw [hvol]
        ring
  have hmm : (∫ y : Real, |primeFreeArchG y| ∂mu) <=
      (∫ y : Real, K ∂mu) :=
    MeasureTheory.integral_mono_of_nonneg hnon hKint hbnd
  calc
    (∫ y in Ioc (0 : Real) primeFreeWidth, |primeFreeArchG y|) <=
        (∫ y : Real, K ∂mu) := by simpa [mu] using hmm
    _ = K * primeFreeWidth := hsum_eq
    _ = (1 + bumpA / 5) * primeFreeWidth := by rfl
    _ <= (34 / 135 : Real) * bumpA := by
      unfold primeFreeWidth
      nlinarith [bumpA_ge_nine_fifths]

private lemma primeFreeArchG_mid_integral_le :
    (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth), |primeFreeArchG y|) <=
      (7 / 30 : Real) * bumpA := by
  let mu : Measure Real :=
    volume.restrict (Ioc primeFreeWidth (2 * primeFreeWidth))
  have hmeas : MeasurableSet (Ioc primeFreeWidth (2 * primeFreeWidth)) :=
    measurableSet_Ioc
  have hbnd : (fun y : Real => |primeFreeArchG y|) ≤ᵐ[mu]
      (fun y : Real => primeFreeWidth * bumpA / y) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact primeFreeArchG_abs_le_mid y (le_of_lt hy.1) hy.2
  have hnon : (fun _ : Real => (0 : Real)) ≤ᵐ[mu]
      (fun y : Real => |primeFreeArchG y|) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact abs_nonneg (primeFreeArchG y)
  have hcont : ContinuousOn
      (fun y : Real => primeFreeWidth * bumpA / y)
      (Icc primeFreeWidth (2 * primeFreeWidth)) := by
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact ne_of_gt (primeFreeWidth_pos.trans_le hy.1)
  have hmajorant_on : IntegrableOn
      (fun y : Real => primeFreeWidth * bumpA / y)
      (Ioc primeFreeWidth (2 * primeFreeWidth)) := by
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmajorant : Integrable
      (fun y : Real => primeFreeWidth * bumpA / y) mu := by
    simpa [mu] using hmajorant_on
  have hmm : (∫ y : Real, |primeFreeArchG y| ∂mu) <=
      (∫ y : Real, primeFreeWidth * bumpA / y ∂mu) :=
    MeasureTheory.integral_mono_of_nonneg hnon hmajorant hbnd
  have hmid_exact :
      (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth),
          primeFreeWidth * bumpA / y) =
        primeFreeWidth * bumpA * Real.log 2 := by
    have hab : primeFreeWidth ≤ 2 * primeFreeWidth := by
      nlinarith [primeFreeWidth_pos]
    calc
      (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth),
          primeFreeWidth * bumpA / y) =
          ∫ y in primeFreeWidth..(2 * primeFreeWidth),
            primeFreeWidth * bumpA / y := by
        rw [intervalIntegral.integral_of_le hab]
      _ = primeFreeWidth * bumpA *
          (∫ y in primeFreeWidth..(2 * primeFreeWidth), 1 / y) := by
        rw [show (fun y : Real => primeFreeWidth * bumpA / y) =
            (fun y : Real => (primeFreeWidth * bumpA) * (1 / y)) by
              funext y
              ring]
        rw [intervalIntegral.integral_const_mul]
      _ = primeFreeWidth * bumpA *
          Real.log ((2 * primeFreeWidth) / primeFreeWidth) := by
        have hzero : (0 : Real) ∉ Set.uIcc primeFreeWidth (2 * primeFreeWidth) :=
          notMem_uIcc_of_lt primeFreeWidth_pos
            (by nlinarith [primeFreeWidth_pos])
        simp only [one_div]
        rw [integral_inv hzero]
      _ = primeFreeWidth * bumpA * Real.log 2 := by
        congr 2
        field_simp [primeFreeWidth_pos.ne']
  calc
    (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth), |primeFreeArchG y|) <=
        (∫ y : Real, primeFreeWidth * bumpA / y ∂mu) := by
      simpa [mu] using hmm
    _ = primeFreeWidth * bumpA * Real.log 2 := hmid_exact
    _ <= primeFreeWidth * bumpA * (7 / 10 : Real) := by
      have hlog : Real.log 2 ≤ (7 / 10 : Real) := by
        exact (Real.log_two_lt_d9.trans_le (by norm_num)).le
      exact mul_le_mul_of_nonneg_left
        hlog
        (mul_nonneg primeFreeWidth_pos.le bumpA_pos.le)
    _ = (7 / 30 : Real) * bumpA := by
      unfold primeFreeWidth
      ring

private lemma primeFree_den_inv_le_exp
    (y : Real) (hy : 2 * primeFreeWidth <= y) :
    1 / den y <=
      Real.exp (-y) / (1 - Real.exp (-(4 / 3 : Real))) := by
  have hy0 : 0 < y :=
    lt_of_lt_of_le (mul_pos (by norm_num) primeFreeWidth_pos) hy
  have hD0 : 0 < 1 - Real.exp (-(4 / 3 : Real)) := by
    have hlt : Real.exp (-(4 / 3 : Real)) < (1 : Real) := by
      simpa using (Real.exp_lt_exp.mpr (by norm_num : (-(4 / 3 : Real)) < 0))
    linarith
  have hD : 0 < 1 - Real.exp (-2 * y) := by
    have hlt : Real.exp (-2 * y) < (1 : Real) := by
      simpa using (Real.exp_lt_exp.mpr (by linarith : (-2 * y) < 0))
    linarith
  have hDle : 1 - Real.exp (-(4 / 3 : Real)) <=
      1 - Real.exp (-2 * y) := by
    have harg : (-2 * y : Real) <= -(4 / 3 : Real) := by
      unfold primeFreeWidth at hy
      linarith
    have hexp : Real.exp (-2 * y) <= Real.exp (-(4 / 3 : Real)) :=
      Real.exp_le_exp.mpr harg
    linarith
  have hinv : 1 / (1 - Real.exp (-2 * y)) <=
      1 / (1 - Real.exp (-(4 / 3 : Real))) :=
    one_div_le_one_div_of_le hD0 hDle
  have hfactor : den y = Real.exp y * (1 - Real.exp (-2 * y)) := by
    unfold den
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1 <;> ring
  have hrewrite : 1 / den y =
      Real.exp (-y) / (1 - Real.exp (-2 * y)) := by
    rw [hfactor]
    field_simp [hD.ne', Real.exp_ne_zero]
    rw [← Real.exp_add]
    norm_num
  calc
    1 / den y = Real.exp (-y) / (1 - Real.exp (-2 * y)) := hrewrite
    _ = Real.exp (-y) * (1 / (1 - Real.exp (-2 * y))) := by
      rw [div_eq_mul_one_div]
    _ <= Real.exp (-y) *
        (1 / (1 - Real.exp (-(4 / 3 : Real)))) := by
      exact mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
    _ = Real.exp (-y) / (1 - Real.exp (-(4 / 3 : Real))) := by
      rw [div_eq_mul_one_div]
      ring

private lemma primeFree_tail_constant_le :
    (2 * primeFreeWidth) *
        (Real.exp (-(2 * primeFreeWidth)) /
          (1 - Real.exp (-(4 / 3 : Real)))) <=
      (7 / 15 : Real) := by
  unfold primeFreeWidth
  let u : Real := Real.exp (-(2 / 3 : Real))
  have hu : u < (19 / 37 : Real) := by
    dsimp [u]
    rw [Real.exp_neg]
    have h := one_div_lt_one_div_of_lt
      (by norm_num : (0 : Real) < 37 / 19) exp_two_thirds_gt
    norm_num at h ⊢
    exact h
  have hsq : Real.exp (-(4 / 3 : Real)) = u ^ 2 := by
    dsimp [u]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq_lt : u ^ 2 < (19 / 37 : Real) ^ 2 := by
    exact (sq_lt_sq₀ (by positivity) (by norm_num)).2 hu
  have hden_u : 0 < 1 - u ^ 2 := by
    nlinarith [hsq_lt]
  have hden_r : 0 < 1 - (19 / 37 : Real) ^ 2 := by norm_num
  have hratio : u / (1 - u ^ 2) <=
      (19 / 37 : Real) / (1 - (19 / 37 : Real) ^ 2) := by
    calc
      u / (1 - u ^ 2) <= (19 / 37 : Real) / (1 - u ^ 2) :=
        div_le_div_of_nonneg_right hu.le hden_u.le
      _ = (19 / 37 : Real) * (1 / (1 - u ^ 2)) := by
        rw [div_eq_mul_one_div]
      _ <= (19 / 37 : Real) *
          (1 / (1 - (19 / 37 : Real) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le hden_r (by linarith [hsq_lt]))
          (by norm_num)
      _ = (19 / 37 : Real) / (1 - (19 / 37 : Real) ^ 2) := by
        rw [div_eq_mul_one_div]
        ring
  have hu_arg : Real.exp (-(2 * (1 / 3 : Real))) = u := by
    dsimp [u]
    congr 1
    ring
  rw [hsq, hu_arg]
  rw [show (2 : Real) * (1 / 3) = 2 / 3 by norm_num]
  calc
    (2 / 3 : Real) * (u / (1 - u ^ 2)) <=
        (2 / 3 : Real) *
          ((19 / 37 : Real) / (1 - (19 / 37 : Real) ^ 2)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ <= (7 / 15 : Real) := by norm_num

private lemma primeFreeArchG_tail_integral_le :
    (∫ y in Ioi (2 * primeFreeWidth), |primeFreeArchG y|) <=
      (7 / 15 : Real) * bumpA := by
  let mu : Measure Real := volume.restrict (Ioi (2 * primeFreeWidth))
  let cden : Real := 1 - Real.exp (-(4 / 3 : Real))
  have hcden : 0 < cden := by
    unfold cden
    have hlt : Real.exp (-(4 / 3 : Real)) < (1 : Real) := by
      simpa using (Real.exp_lt_exp.mpr (by norm_num : (-(4 / 3 : Real)) < 0))
    linarith
  have hcden_ne : cden ≠ 0 := ne_of_gt hcden
  have hmeas : MeasurableSet (Ioi (2 * primeFreeWidth)) := isOpen_Ioi.measurableSet
  have hbnd : (fun y : Real => |primeFreeArchG y|) ≤ᵐ[mu]
      (fun y : Real =>
        (2 * primeFreeWidth * bumpA) * (Real.exp (-y) / cden)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    have hy2w : 2 * primeFreeWidth <= y := le_of_lt hy
    rw [primeFreeArchG_abs_eq_tail y hy2w]
    calc
      (2 * primeFreeWidth) * bumpA / den y =
          (2 * primeFreeWidth * bumpA) * (1 / den y) := by
        rw [div_eq_mul_one_div]
      _ <= (2 * primeFreeWidth * bumpA) *
          (Real.exp (-y) / cden) := by
        exact mul_le_mul_of_nonneg_left (primeFree_den_inv_le_exp y hy2w)
          (mul_nonneg (mul_nonneg (by norm_num) primeFreeWidth_pos.le)
            bumpA_pos.le)
  have hnon : (fun _ : Real => (0 : Real)) ≤ᵐ[mu]
      (fun y : Real => |primeFreeArchG y|) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact abs_nonneg (primeFreeArchG y)
  have hexp : Integrable (fun y : Real => Real.exp (-y)) mu := by
    change Integrable (fun y : Real => Real.exp (-y))
      (volume.restrict (Ioi (2 * primeFreeWidth)))
    exact integrableOn_exp_neg_Ioi (2 * primeFreeWidth)
  have hmajorant : Integrable
      (fun y : Real => (2 * primeFreeWidth * bumpA) *
        (Real.exp (-y) / cden)) mu := by
    have hcoax :
        (fun y : Real => (2 * primeFreeWidth * bumpA) *
          (Real.exp (-y) / cden)) =
        (fun y : Real => ((2 * primeFreeWidth * bumpA) / cden) *
          Real.exp (-y)) := by
      funext y
      field_simp [hcden_ne, Real.exp_ne_zero]
    rw [hcoax]
    exact hexp.const_mul ((2 * primeFreeWidth * bumpA) / cden)
  have hmm : (∫ y : Real, |primeFreeArchG y| ∂mu) <=
      (∫ y : Real, (2 * primeFreeWidth * bumpA) *
        (Real.exp (-y) / cden) ∂mu) :=
    MeasureTheory.integral_mono_of_nonneg hnon hmajorant hbnd
  have hright :
      (∫ y : Real, (2 * primeFreeWidth * bumpA) *
        (Real.exp (-y) / cden) ∂mu) =
      (2 * primeFreeWidth * bumpA) *
        (Real.exp (-(2 * primeFreeWidth)) / cden) := by
    calc
      (∫ y : Real, (2 * primeFreeWidth * bumpA) *
          (Real.exp (-y) / cden) ∂mu) =
          ∫ y : Real, ((2 * primeFreeWidth * bumpA) / cden) *
            Real.exp (-y) ∂mu := by
        apply integral_congr_ae
        filter_upwards with y
        field_simp [hcden_ne, Real.exp_ne_zero]
      _ = ((2 * primeFreeWidth * bumpA) / cden) *
          (∫ y : Real, Real.exp (-y) ∂mu) := by
        rw [integral_const_mul]
      _ = ((2 * primeFreeWidth * bumpA) / cden) *
          Real.exp (-(2 * primeFreeWidth)) := by
        rw [show (∫ y : Real, Real.exp (-y) ∂mu) =
            Real.exp (-(2 * primeFreeWidth)) by
              simpa [mu] using integral_exp_neg_Ioi (2 * primeFreeWidth)]
      _ = (2 * primeFreeWidth * bumpA) *
          (Real.exp (-(2 * primeFreeWidth)) / cden) := by
        field_simp [hcden_ne]
  have htail :
      (∫ y in Ioi (2 * primeFreeWidth), |primeFreeArchG y|) <=
        (2 * primeFreeWidth * bumpA) *
          (Real.exp (-(2 * primeFreeWidth)) / cden) := by
    simpa [mu] using hmm.trans_eq hright
  calc
    (∫ y in Ioi (2 * primeFreeWidth), |primeFreeArchG y|) <=
        (2 * primeFreeWidth * bumpA) *
          (Real.exp (-(2 * primeFreeWidth)) / cden) := htail
    _ = bumpA * ((2 * primeFreeWidth) *
          (Real.exp (-(2 * primeFreeWidth)) /
            (1 - Real.exp (-(4 / 3 : Real))))) := by
      unfold cden
      ring
    _ <= bumpA * (7 / 15 : Real) := by
      exact mul_le_mul_of_nonneg_left primeFree_tail_constant_le bumpA_pos.le
    _ = (7 / 15 : Real) * bumpA := by ring

private lemma primeFreeArchG_abs_integral_split :
    (∫ y in Ioi (0 : Real), |primeFreeArchG y|) =
      (∫ y in Ioc (0 : Real) primeFreeWidth, |primeFreeArchG y|) +
        (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth),
          |primeFreeArchG y|) +
        (∫ y in Ioi (2 * primeFreeWidth), |primeFreeArchG y|) := by
  let f : Real → Real := fun y => |primeFreeArchG y|
  have hf : IntegrableOn f (Ioi (0 : Real)) := by
    simpa [f] using primeFreeArchG_abs_integrableOn_Ioi
  have hAint : IntegrableOn f (Ioc (0 : Real) primeFreeWidth) := by
    apply hf.mono_set
    intro y hy
    exact hy.1
  have hBint : IntegrableOn f
      (Ioc primeFreeWidth (2 * primeFreeWidth)) := by
    apply hf.mono_set
    intro y hy
    exact lt_trans primeFreeWidth_pos hy.1
  have hCint : IntegrableOn f (Ioi (2 * primeFreeWidth)) := by
    apply hf.mono_set
    intro y hy
    exact lt_trans (mul_pos (by norm_num) primeFreeWidth_pos) hy
  have hABdisj : Disjoint (Ioc (0 : Real) primeFreeWidth)
      (Ioc primeFreeWidth (2 * primeFreeWidth)) := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    exact (not_lt_of_ge hyA.2) hyB.1
  have hBCdisj : Disjoint (Ioc (0 : Real) (2 * primeFreeWidth))
      (Ioi (2 * primeFreeWidth)) := by
    rw [Set.disjoint_left]
    intro y hyB hyC
    exact (not_lt_of_ge hyB.2) hyC
  have hABset : Ioc (0 : Real) primeFreeWidth ∪
      Ioc primeFreeWidth (2 * primeFreeWidth) =
        Ioc (0 : Real) (2 * primeFreeWidth) := by
    ext y
    rw [Set.mem_union, Set.mem_Ioc, Set.mem_Ioc, Set.mem_Ioc]
    constructor
    · rintro (hy | hy)
      · exact ⟨hy.1, hy.2.trans (by nlinarith [primeFreeWidth_pos])⟩
      · exact ⟨lt_trans primeFreeWidth_pos hy.1, hy.2⟩
    · intro hy
      by_cases hle : y <= primeFreeWidth
      · exact Or.inl ⟨hy.1, hle⟩
      · exact Or.inr ⟨lt_of_not_ge hle, hy.2⟩
  have hBCset : Ioc (0 : Real) (2 * primeFreeWidth) ∪
      Ioi (2 * primeFreeWidth) = Ioi (0 : Real) := by
    ext y
    rw [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi, Set.mem_Ioi]
    constructor
    · rintro (hy | hy)
      · exact hy.1
      · exact lt_trans (mul_pos (by norm_num) primeFreeWidth_pos) hy
    · intro hy
      by_cases hle : y <= 2 * primeFreeWidth
      · exact Or.inl ⟨hy, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
  have hABint : IntegrableOn f
      (Ioc (0 : Real) (2 * primeFreeWidth)) := by
    apply hf.mono_set
    intro y hy
    exact hy.1
  have hsplitAB :
      (∫ y in Ioc (0 : Real) (2 * primeFreeWidth), f y) =
        (∫ y in Ioc (0 : Real) primeFreeWidth, f y) +
          (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth), f y) := by
    rw [← hABset]
    exact MeasureTheory.setIntegral_union hABdisj measurableSet_Ioc hAint hBint
  have hsplitBC :
      (∫ y in Ioi (0 : Real), f y) =
        (∫ y in Ioc (0 : Real) (2 * primeFreeWidth), f y) +
          (∫ y in Ioi (2 * primeFreeWidth), f y) := by
    rw [← hBCset]
    exact MeasureTheory.setIntegral_union hBCdisj measurableSet_Ioi hABint hCint
  calc
    (∫ y in Ioi (0 : Real), |primeFreeArchG y|) =
        (∫ y in Ioi (0 : Real), f y) := by rfl
    _ = (∫ y in Ioc (0 : Real) (2 * primeFreeWidth), f y) +
          (∫ y in Ioi (2 * primeFreeWidth), f y) := hsplitBC
    _ = (∫ y in Ioc (0 : Real) primeFreeWidth, f y) +
          (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth), f y) +
          (∫ y in Ioi (2 * primeFreeWidth), f y) := by rw [hsplitAB]
    _ = (∫ y in Ioc (0 : Real) primeFreeWidth, |primeFreeArchG y|) +
          (∫ y in Ioc primeFreeWidth (2 * primeFreeWidth),
            |primeFreeArchG y|) +
          (∫ y in Ioi (2 * primeFreeWidth), |primeFreeArchG y|) := by rfl

private lemma primeFreeArchG_abs_integral_le :
    (∫ y in Ioi (0 : Real), |primeFreeArchG y|) <=
      (257 / 270 : Real) * bumpA := by
  have hnear := primeFreeArchG_near_integral_le
  have hmid := primeFreeArchG_mid_integral_le
  have htail := primeFreeArchG_tail_integral_le
  rw [primeFreeArchG_abs_integral_split]
  nlinarith [hnear, hmid, htail]

private lemma primeFree_archimedean_integral_abs_re_le :
    |(∫ y in Ioi (0 : Real),
        primeFreeSelectedOwner.archimedeanIntegrand y).re| <=
      ∫ y in Ioi (0 : Real), |primeFreeArchG y| := by
  let mu : Measure Real := volume.restrict (Ioi (0 : Real))
  have hmeas : MeasurableSet (Ioi (0 : Real)) := isOpen_Ioi.measurableSet
  have hchain :
      |(∫ y : Real, primeFreeSelectedOwner.archimedeanIntegrand y ∂mu).re| <=
        ∫ y : Real, |primeFreeArchG y| ∂mu := by
    calc
      |(∫ y : Real, primeFreeSelectedOwner.archimedeanIntegrand y ∂mu).re| <=
          ‖∫ y : Real, primeFreeSelectedOwner.archimedeanIntegrand y ∂mu‖ :=
        Complex.abs_re_le_norm _
      _ <= ∫ y : Real,
          ‖primeFreeSelectedOwner.archimedeanIntegrand y‖ ∂mu :=
        MeasureTheory.norm_integral_le_integral_norm
          (fun y : Real => primeFreeSelectedOwner.archimedeanIntegrand y)
      _ = ∫ y : Real, |primeFreeArchG y| ∂mu := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
        have hy0 : 0 < y := by exact hy
        exact primeFree_archimedeanIntegrand_norm_eq_abs y hy0
  change |(∫ y : Real,
      primeFreeSelectedOwner.archimedeanIntegrand y ∂mu).re| <=
        ∫ y : Real, |primeFreeArchG y| ∂mu
  exact hchain

private lemma primeFree_archimedean_integral_abs_re_bound :
    |(∫ y in Ioi (0 : Real),
        primeFreeSelectedOwner.archimedeanIntegrand y).re| <=
      (257 / 270 : Real) * bumpA := by
  calc
    |(∫ y in Ioi (0 : Real),
        primeFreeSelectedOwner.archimedeanIntegrand y).re| <=
        ∫ y in Ioi (0 : Real), |primeFreeArchG y| :=
      primeFree_archimedean_integral_abs_re_le
    _ <= (257 / 270 : Real) * bumpA :=
      primeFreeArchG_abs_integral_le

private theorem primeFreePlateau_selected_archimedeanTerm_re_pos :
    0 < (primeFreeSelectedOwner.archimedeanTerm).re := by
  rw [ConnesWeilRH.Source.CCM25Concrete.archimedeanTerm_re_eq_lead_add_integral]
  let C : Real := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant
  let A : Real := bumpA
  let J : Real :=
    (∫ y in Ioi (0 : Real), primeFreeSelectedOwner.archimedeanIntegrand y).re
  have hC : (29 / 10 : Real) < C := by
    simpa [C] using ConnesWeilRH.Source.Dev.Wall14Coeff.archCoeff_gt
  have hA : 0 < A := by simpa [A] using bumpA_pos
  have hmass :
      (primeFreeSelectedOwner.convolutionSquare.test 0).re =
        primeFreeWidth * A := by
    change ((wideTest primeFreeWidth primeFreeWidth_pos).convolutionSquare.test 0).re =
      primeFreeWidth * bumpA
    exact wideTest_convolutionSquare_zero_re_eq_scaled_bumpA
      primeFreeWidth primeFreeWidth_pos
  have hJ : |J| <= (257 / 270 : Real) * A := by
    simpa [J, A] using primeFree_archimedean_integral_abs_re_bound
  have hlead : (257 / 270 : Real) * A < C *
      (primeFreeSelectedOwner.convolutionSquare.test 0).re := by
    calc
      (257 / 270 : Real) * A < (29 / 10 : Real) * (A / 3) := by
        nlinarith
      _ < C * (A / 3) := by
        exact mul_lt_mul_of_pos_right hC (by positivity)
      _ = C * (primeFreeSelectedOwner.convolutionSquare.test 0).re := by
        rw [hmass]
        unfold primeFreeWidth
        ring
  have hJlower : -((257 / 270 : Real) * A) <= J := by
    exact (abs_le.mp hJ).1
  nlinarith [hlead, hJlower]

theorem primeFreePlateau_archimedeanTerm_pos :
    0 < C1SameOwnerWeil.archimedeanTerm primeFreePlateau.convolutionSquare := by
  rw [C1SameOwnerWeil.archimedeanTerm_square_eq_selected]
  simpa [primeFreeSelectedOwner] using
    primeFreePlateau_selected_archimedeanTerm_re_pos

theorem primeFreePlateau_square_support :
    Function.support primeFreePlateau.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
  have hwidth : 2 * primeFreeWidth < Real.log 2 := by
    unfold primeFreeWidth
    nlinarith [Real.log_two_gt_d9]
  have hsquare :=
    wideTest_convolutionSquare_support_subset_open_double
      primeFreeWidth primeFreeWidth_pos
  intro x hx
  rcases hsquare hx with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- The narrow plateau retains a positive square mass, with the explicit
lower bound inherited from the width-one plateau. -/
theorem primeFreePlateau_square_mass_ge_three_fifths :
    (3 / 5 : Real) <= (primeFreePlateau.convolutionSquare.test 0).re := by
  change (3 / 5 : Real) <=
    ((wideTest primeFreeWidth primeFreeWidth_pos).convolutionSquare.test 0).re
  rw [wideTest_convolutionSquare_zero_re_eq_scaled_bumpA]
  unfold primeFreeWidth
  nlinarith [bumpA_ge_nine_fifths]

/-- The same scaled plateau has an explicit upper mass bound. -/
theorem primeFreePlateau_square_mass_le_two_thirds :
    (primeFreePlateau.convolutionSquare.test 0).re <= (2 / 3 : Real) := by
  change ((wideTest primeFreeWidth primeFreeWidth_pos).convolutionSquare.test 0).re <=
    (2 / 3 : Real)
  rw [wideTest_convolutionSquare_zero_re_eq_scaled_bumpA]
  unfold primeFreeWidth
  nlinarith [bumpA_le_two]

/-- At width `1 / 3`, the square profile is zero from height `2 / 3` onward. -/
theorem primeFreePlateau_square_re_eq_zero_of_two_thirds_le_abs
    (y : Real) (hy : (2 / 3 : Real) <= |y|) :
    (primeFreePlateau.convolutionSquare.test y).re = 0 := by
  change ((wideTest primeFreeWidth primeFreeWidth_pos).convolutionSquare.test y).re = 0
  apply wideTest_convolutionSquare_re_eq_zero_of_two_mul_w_le_abs
    primeFreeWidth primeFreeWidth_pos y
  simpa [primeFreeWidth] using hy

end C1HealthyNarrowPlateau
end Source
end ConnesWeilRH
