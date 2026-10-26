import ConnesWeilRH.Dev.C1RouteBPrimeFourierReadback3120
import ConnesWeilRH.Dev.C1C3SigmaKernel

namespace ConnesWeilRH.Source.C1RouteBArchimedeanFourierReadback3121

open MeasureTheory Complex Filter Set
open CCM25Concrete.CompactLogConvolution CC20YoshidaConvolution
open C1RouteBPrimeFourierReadback3120 C1XiArithmeticPrimePowerReadback
open C1XiCenterTwoGamma C1XiCenterTwoPole C1SameOwnerWeil
open C1RouteBAdaptivePoweredTail3117 C1FourPointSpectralPrefixTransport
open C1TwoPointSpectralDecomposition
open ConnesWeilRH.Dev
open scoped FourierTransform BigOperators Topology

noncomputable section

def quarterPoint3121 (xi : ℝ) : ℂ := 1 / 4 + cyclePoint3120 xi / 2

def reciprocal3121 (n : ℕ) (xi : ℝ) : ℂ :=
  ((n : ℂ) + quarterPoint3121 xi)⁻¹ - ((n : ℂ) + 1 / 2)⁻¹

def weightedEnergy3121 (g : CompactLogTest) (xi : ℝ) : ℝ :=
  (1 + Real.pi * |xi|) * energy3120 g xi

theorem weightedEnergy_integrable3121 (g : CompactLogTest) :
    Integrable (weightedEnergy3121 g) := by
  have h0 : Integrable (energy3120 g) := by
    simpa only [mul_zero, Real.cos_zero, one_mul] using cosine_energy_integrable3120 g 0
  have h1 := (𝓕 g.convolutionSquare.test).integrable_pow_mul volume 1
  have hnorm (xi : ℝ) : ‖(𝓕 g.convolutionSquare.test) xi‖ = energy3120 g xi := by
    rw [square_fourier_eq_energy3120, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    rfl
  simp only [pow_one, Real.norm_eq_abs, hnorm] at h1
  apply (h0.add (h1.const_mul Real.pi)).congr
  filter_upwards with xi
  simp only [Pi.add_apply, weightedEnergy3121]
  ring

theorem quarterPoint_re3121 (xi : ℝ) : (quarterPoint3121 xi).re = 1 / 4 := by
  simp [quarterPoint3121, cyclePoint3120, Complex.mul_re]

theorem norm_reciprocal_le3121 (n : ℕ) (xi : ℝ) :
    ‖reciprocal3121 n xi‖ ≤
      (1 + Real.pi * |xi|) / (((n : ℝ) + 1 / 4) * ((n : ℝ) + 1 / 2)) := by
  let a : ℂ := (n : ℂ) + quarterPoint3121 xi
  let b : ℂ := (n : ℂ) + 1 / 2
  have ha : a.re = (n : ℝ) + 1 / 4 := by simp [a, quarterPoint_re3121]
  have hb : b.re = (n : ℝ) + 1 / 2 := by simp [b]
  have hap : 0 < a.re := by rw [ha]; positivity
  have hbp : 0 < b.re := by rw [hb]; positivity
  have ha0 : a ≠ 0 := by intro h; simp [h] at hap
  have hb0 : b ≠ 0 := by intro h; simp [h] at hbp
  have hna : (n : ℝ) + 1 / 4 ≤ ‖a‖ := by
    rw [← ha]; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hnb : (n : ℝ) + 1 / 2 ≤ ‖b‖ := by
    rw [← hb]; exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hnum : ‖b - a‖ ≤ 1 + Real.pi * |xi| := by
    have heq : b - a = (1 / 4 : ℂ) - cyclePoint3120 xi / 2 := by
      dsimp [a, b, quarterPoint3121]; ring
    rw [heq]
    calc
      _ ≤ ‖(1 / 4 : ℂ)‖ + ‖cyclePoint3120 xi / 2‖ := norm_sub_le _ _
      _ ≤ 1 + Real.pi * |xi| := by
        simp [cyclePoint3120, abs_of_pos Real.pi_pos]
        ring_nf
        norm_num
  have hid : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  change ‖a⁻¹ - b⁻¹‖ ≤ _
  rw [hid, norm_div, norm_mul]
  calc
    _ ≤ (1 + Real.pi * |xi|) / (‖a‖ * ‖b‖) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hna hnb (by positivity) (norm_nonneg _))

theorem reciprocal_energy_integrable3121 (g : CompactLogTest) (n : ℕ) :
    Integrable (fun xi : ℝ => reciprocal3121 n xi * (energy3120 g xi : ℂ)) := by
  have h := (weightedEnergy_integrable3121 g).div_const
    (((n : ℝ) + 1 / 4) * ((n : ℝ) + 1 / 2))
  apply h.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · have hq : Continuous quarterPoint3121 := by
        unfold quarterPoint3121 cyclePoint3120
        fun_prop
      have hnz (xi : ℝ) : (n : ℂ) + quarterPoint3121 xi ≠ 0 := by
        apply ne_of_apply_ne Complex.re
        simp only [Complex.add_re, Complex.natCast_re, quarterPoint_re3121, Complex.zero_re]
        positivity
      exact ((continuous_const.add hq).inv₀ hnz).sub continuous_const
    · unfold energy3120
      fun_prop
  · filter_upwards with xi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [weightedEnergy3121, div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right (norm_reciprocal_le3121 n xi) (sq_nonneg _)

theorem summable_integral_norm_reciprocal_energy3121 (g : CompactLogTest) :
    Summable (fun n : ℕ => ∫ xi : ℝ,
      ‖reciprocal3121 n xi * (energy3120 g xi : ℂ)‖) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ *
      ∫ xi : ℝ, weightedEnergy3121 g xi) :=
    ((Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)).mul_right _
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound (xi : ℝ) : ‖reciprocal3121 n xi * (energy3120 g xi : ℂ)‖ ≤
      ((n : ℝ) ^ 2)⁻¹ * weightedEnergy3121 g xi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hden : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1 / 4) * ((n : ℝ) + 1 / 2) := by
      nlinarith
    have hrec := (norm_reciprocal_le3121 n xi).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
    convert mul_le_mul_of_nonneg_right hrec (sq_nonneg ‖(𝓕 g.test) xi‖) using 1 <;>
      simp only [energy3120, weightedEnergy3121, div_eq_mul_inv] <;> ring
  have hle := integral_mono_ae (reciprocal_energy_integrable3121 g n).norm
    ((weightedEnergy_integrable3121 g).const_mul ((n : ℝ) ^ 2)⁻¹)
    (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul] at hle
  have hp : 0 ≤ ∫ xi : ℝ, ‖reciprocal3121 n xi * (energy3120 g xi : ℂ)‖ :=
    integral_nonneg (fun xi => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  exact hle

theorem summable_reciprocal3121 (xi : ℝ) : Summable (fun n : ℕ => reciprocal3121 n xi) := by
  have h := summable_halfAnchorGaussReciprocalSeries
    (z := quarterPoint3121 xi) (by rw [quarterPoint_re3121]; norm_num)
  convert h.neg using 1
  funext n
  simp only [reciprocal3121, neg_sub]

theorem sigma_eq_reciprocal_series3121 (xi : ℝ) :
    c3Sigma (2 * Real.pi * xi) = Real.log (4 * Real.pi) + Real.eulerMascheroniConstant +
      (∑' n : ℕ, reciprocal3121 n xi).re := by
  have h := halfAnchorGaussReciprocalSeries_eq_digamma_sub_half_of_pos
    (z := quarterPoint3121 xi) (by rw [quarterPoint_re3121]; norm_num)
  have hneg : (∑' n : ℕ, reciprocal3121 n xi) =
      Complex.digamma (1 / 2 : ℂ) - Complex.digamma (quarterPoint3121 xi) := by
    calc
      _ = -(∑' n : ℕ, (((n : ℂ) + 1 / 2)⁻¹ -
          ((n : ℂ) + quarterPoint3121 xi)⁻¹)) := by
        rw [← tsum_neg]
        congr 1
        funext n
        simp only [reciprocal3121, neg_sub]
      _ = _ := by rw [h]; ring
  rw [hneg]
  have hquarter : quarterPoint3121 xi =
      (((1 / 4 : ℝ) : ℂ) - (((2 * Real.pi * xi : ℝ) : ℂ) * I) / 2) := by
    unfold quarterPoint3121 cyclePoint3120
    push_cast
    ring
  have hhalf : (Complex.digamma (1 / 2 : ℂ)).re =
      -2 * Real.log 2 - Real.eulerMascheroniConstant := by
    rw [Complex.digamma_one_half]
    norm_num [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.log_ofReal_re]
    exact Complex.log_ofReal_re 2
  rw [Complex.sub_re, hhalf, hquarter]
  unfold c3Sigma
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero,
    show Real.log 4 = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
  ring

theorem cycle_resolvent_readback3121 (F : CompactLogTest) {a : ℝ} (ha : 0 < a) :
    (∫ xi : ℝ, (𝓕 F.test) xi / ((a : ℂ) + cyclePoint3120 xi)) =
      ∫ y : ℝ in Ioi 0, Complex.exp (-((a : ℂ) * (y : ℂ))) * F.test y := by
  let f : ℝ → ℂ := fun t => fourierLaplace F.test t / ((a : ℂ) + (t : ℂ) * I)
  have hscale : |((-2 * Real.pi)⁻¹ : ℝ)| = (2 * Real.pi)⁻¹ := by
    rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) by ring, inv_neg, abs_neg,
      abs_of_pos (inv_pos.mpr (by positivity))]
  have hchange := Measure.integral_comp_mul_left f (-2 * Real.pi)
  have harg (xi : ℝ) : -((-2 * Real.pi * xi) / (2 * Real.pi)) = xi := by
    field_simp [Real.pi_ne_zero]
  have heq : (fun xi : ℝ => f ((-2 * Real.pi) * xi)) =
      (fun xi : ℝ => (𝓕 F.test) xi / ((a : ℂ) + cyclePoint3120 xi)) := by
    funext xi
    simp only [f, fourierLaplace_eq_fourier, harg, cyclePoint3120]
  rw [heq, hscale, Complex.real_smul] at hchange
  rw [show (∫ t : ℝ, f t) = (2 * (Real.pi : ℂ)) *
      (∫ y : ℝ in Ioi 0, Complex.exp (-((a : ℂ) * (y : ℂ))) * F.test y) from
    by simpa only [f, neg_mul] using integral_fourierLaplace_div_vertical F.test ha] at hchange
  rw [hchange]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp

theorem reciprocal_sum_integrable3121 (owner : CompactLogTest) :
    Integrable (fun t : Real => ∑' n : Nat, reciprocal3121 n t * (energy3120 owner t : ℂ)) := by
  let g : Nat → Real → Complex := fun n t => reciprocal3121 n t * (energy3120 owner t : ℂ)
  have hg : ∀ n, Integrable (g n) := fun n =>
    reciprocal_energy_integrable3121 owner n
  have hsumNorm : Summable (fun n : Nat =>
      ∫ t : Real, norm (g n t)) :=
    summable_integral_norm_reciprocal_energy3121 owner
  have hsumAE : AEStronglyMeasurable
      (fun t : Real => tsum fun n : Nat => g n t) :=
    AEStronglyMeasurable.tsum (fun n => (hg n).aestronglyMeasurable)
  have hfinite : HasFiniteIntegral
      (fun t : Real => tsum fun n : Nat => g n t) := by
    rw [HasFiniteIntegral]
    have hmeasNorm (n : Nat) : AEMeasurable (fun t : Real =>
        enorm (g n t)) := (hg n).aestronglyMeasurable.enorm
    have hlin :
        (∫⁻ t : Real, enorm (∑' n : Nat, g n t)) <=
          tsum (fun n : Nat => ∫⁻ t : Real, enorm (g n t)) := by
      calc
        _ <= ∫⁻ t : Real, ∑' n : Nat, enorm (g n t) := by
          apply lintegral_mono_ae
          filter_upwards with t
          exact enorm_tsum_le_tsum_enorm
        _ = tsum (fun n : Nat => ∫⁻ t : Real, enorm (g n t)) := by
          rw [lintegral_tsum hmeasNorm]
    have hlinFinite :
        tsum (fun n : Nat => ∫⁻ t : Real, enorm (g n t)) ≠ ⊤ := by
      have hterm (n : Nat) :
          (∫⁻ t : Real, enorm (g n t)) =
            ENNReal.ofReal (∫ t : Real, norm (g n t)) := by
        exact (ofReal_integral_norm_eq_lintegral_enorm (hg n)).symm
      rw [tsum_congr hterm]
      exact hsumNorm.tsum_ofReal_ne_top
    exact hlin.trans_lt (lt_top_iff_ne_top.mpr hlinFinite)
  exact ⟨hsumAE, hfinite⟩

theorem sigma_energy_integrable3121 (g : CompactLogTest) :
    Integrable (fun xi : ℝ => c3Sigma (2 * Real.pi * xi) * energy3120 g xi) := by
  have h0 : Integrable (energy3120 g) := by
    simpa only [mul_zero, Real.cos_zero, one_mul] using cosine_energy_integrable3120 g 0
  have hr := (reciprocal_sum_integrable3121 g).re
  change Integrable (fun xi : ℝ =>
    (∑' n : ℕ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re) at hr
  apply ((h0.const_mul (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)).add hr).congr
  filter_upwards with xi
  simp only [Pi.add_apply, tsum_mul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, sigma_eq_reciprocal_series3121]
  ring

theorem exp_test_integrable3121 (F : CompactLogTest) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Complex.exp (-((a : ℂ) * (y : ℂ))) * F.test y) (Ioi 0) := by
  have h : IntegrableOn (fun y : ℝ => F.test y) (Ioi 0) := F.test.integrable.integrableOn
  have hp := h.mul_bdd (g := fun y : ℝ => Complex.exp (-((a : ℂ) * (y : ℂ))))
    (c := 1) (by fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le hy.le)))
  apply hp.congr
  filter_upwards with y
  ring

theorem profile_integral_re3121 (g : CompactLogTest) (n : ℕ) :
    (∫ y : ℝ in Ioi 0, gammaRArchProfileTerm g.convolutionSquare n y).re =
      (∫ xi : ℝ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re := by
  let a : ℝ := 2 * (n : ℝ) + 1 / 2
  let b : ℝ := 2 * (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have h0 : Integrable (energy3120 g) := by
    simpa only [mul_zero, Real.cos_zero, one_mul] using cosine_energy_integrable3120 g 0
  have hres : Integrable (fun xi : ℝ =>
      (energy3120 g xi : ℂ) / ((a : ℂ) + cyclePoint3120 xi)) := by
    have he : Integrable (fun xi : ℝ => (energy3120 g xi : ℂ)) := h0.ofReal
    apply he.mul_bdd (g := fun xi : ℝ => ((a : ℂ) + cyclePoint3120 xi)⁻¹)
      (c := a⁻¹)
    · have hnz (xi : ℝ) : (a : ℂ) + cyclePoint3120 xi ≠ 0 := by
        apply ne_of_apply_ne Complex.re
        simpa [cyclePoint3120, Complex.mul_re] using ha.ne'
      exact ((by unfold cyclePoint3120; fun_prop :
        Continuous (fun xi : ℝ => (a : ℂ) + cyclePoint3120 xi)).inv₀ hnz).aestronglyMeasurable
    · filter_upwards with xi
      rw [norm_inv]
      simp only [← one_div]
      apply one_div_le_one_div_of_le ha
      have hr : ((a : ℂ) + cyclePoint3120 xi).re = a := by simp [cyclePoint3120]
      calc
        a = ((a : ℂ) + cyclePoint3120 xi).re := hr.symm
        _ ≤ ‖(a : ℂ) + cyclePoint3120 xi‖ :=
          (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hrational (xi : ℝ) : reciprocal3121 n xi * (energy3120 g xi : ℂ) =
      2 * ((energy3120 g xi : ℂ) / ((a : ℂ) + cyclePoint3120 xi)) -
        (2 / (b : ℂ)) * (energy3120 g xi : ℂ) := by
    have hq : (n : ℂ) + quarterPoint3121 xi = ((a : ℂ) + cyclePoint3120 xi) / 2 := by
      dsimp [a, quarterPoint3121]
      push_cast
      ring
    have hbb : (n : ℂ) + 1 / 2 = (b : ℂ) / 2 := by
      dsimp [b]
      push_cast
      ring
    unfold reciprocal3121
    rw [hq, hbb, inv_div, inv_div]
    ring
  have hinter : (∫ xi : ℝ, reciprocal3121 n xi * (energy3120 g xi : ℂ)) =
      2 * (∫ y : ℝ in Ioi 0, Complex.exp (-((a : ℂ) * (y : ℂ))) *
        g.convolutionSquare.test y) - (2 / (b : ℂ)) *
          ((g.convolutionSquare.test 0).re : ℂ) := by
    have heC : Integrable (fun xi : ℝ => (energy3120 g xi : ℂ)) := h0.ofReal
    simp_rw [hrational]
    rw [integral_sub (hres.const_mul (2 : ℂ)) (heC.const_mul (2 / (b : ℂ))),
      integral_const_mul, integral_const_mul, integral_complex_ofReal]
    have hmass : (∫ xi : ℝ, energy3120 g xi) = (g.convolutionSquare.test 0).re := by
      simpa only [mul_zero, Real.cos_zero, one_mul] using
        (square_re_eq_cosine_integral3120 g 0).symm
    rw [hmass]
    rw [← cycle_resolvent_readback3121 g.convolutionSquare ha]
    simp only [square_fourier_eq_energy3120, energy3120]
  rw [hinter]
  have hprofile := integral_re (integrableOn_gammaRArchProfileTerm_public g.convolutionSquare n)
  change (∫ y : ℝ in Ioi 0, (gammaRArchProfileTerm g.convolutionSquare n y).re) =
    (∫ y : ℝ in Ioi 0, gammaRArchProfileTerm g.convolutionSquare n y).re at hprofile
  rw [← hprofile]
  have hexp (c y : ℝ) : Complex.exp (-((c : ℂ) * (y : ℂ))) =
      (Real.exp (-(c * y)) : ℂ) := by rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_exp]
  have hpoint (y : ℝ) : (gammaRArchProfileTerm g.convolutionSquare n y).re =
      2 * (Complex.exp (-((a : ℂ) * (y : ℂ))) * g.convolutionSquare.test y).re -
      2 * (Complex.exp (-((b : ℂ) * (y : ℂ)))).re * (g.convolutionSquare.test 0).re := by
    change (Complex.exp (-((a : ℂ) * (y : ℂ))) *
      (g.convolutionSquare.test y + g.convolutionSquare.test (-y)) -
      2 * Complex.exp (-((b : ℂ) * (y : ℂ))) * g.convolutionSquare.test 0).re = _
    rw [g.convolutionSquare_neg, hexp a y, hexp b y]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero]
    rw [g.convolutionSquare_zero_im]
    ring
  simp_rw [hpoint]
  have he := exp_test_integrable3121 g.convolutionSquare ha
  have hbexp : IntegrableOn (fun y : ℝ => Complex.exp (-((b : ℂ) * (y : ℂ)))) (Ioi 0) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_complex_Ioi (a := -(b : ℂ)) (by simpa using hb) 0)
  have heRe := integral_re he
  have hbRe := integral_re hbexp
  have heR : IntegrableOn (fun y : ℝ => (Complex.exp (-((a : ℂ) * (y : ℂ))) *
    g.convolutionSquare.test y).re) (Ioi 0) := he.re
  have hbR : IntegrableOn (fun y : ℝ => (Complex.exp (-((b : ℂ) * (y : ℂ)))).re) (Ioi 0) := hbexp.re
  change (∫ y : ℝ in Ioi 0, (Complex.exp (-((a : ℂ) * (y : ℂ))) *
    g.convolutionSquare.test y).re) =
      (∫ y : ℝ in Ioi 0, Complex.exp (-((a : ℂ) * (y : ℂ))) * g.convolutionSquare.test y).re at heRe
  change (∫ y : ℝ in Ioi 0, (Complex.exp (-((b : ℂ) * (y : ℂ)))).re) =
    (∫ y : ℝ in Ioi 0, Complex.exp (-((b : ℂ) * (y : ℂ)))).re at hbRe
  rw [integral_sub (heR.const_mul 2) ((hbR.const_mul 2).mul_const ((g.convolutionSquare.test 0).re)),
    integral_const_mul, integral_mul_const, integral_const_mul, heRe, hbRe,
    integral_exp_neg_mul_complex_Ioi (by simpa using hb)]
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.inv_re, Complex.normSq_apply,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  field_simp
  <;> ring

theorem integral_sigma_eq_series3121 (g : CompactLogTest) :
    (∫ xi : ℝ, c3Sigma (2 * Real.pi * xi) * energy3120 g xi) =
      (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
        (g.convolutionSquare.test 0).re +
      ∑' n : ℕ, (∫ xi : ℝ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re := by
  have h0 : Integrable (energy3120 g) := by
    simpa only [mul_zero, Real.cos_zero, one_mul] using cosine_energy_integrable3120 g 0
  have hsum := reciprocal_sum_integrable3121 g
  have hsumR : Integrable (fun xi : ℝ =>
    (∑' n : ℕ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re) := hsum.re
  have hexchange := (integral_tsum_of_summable_integral_norm
    (fun n => reciprocal_energy_integrable3121 g n)
    (summable_integral_norm_reciprocal_energy3121 g)).symm
  have hs : Summable (fun n : ℕ =>
      ∫ xi : ℝ, reciprocal3121 n xi * (energy3120 g xi : ℂ)) :=
    (summable_integral_norm_reciprocal_energy3121 g).of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have hpoint : (fun xi : ℝ => c3Sigma (2 * Real.pi * xi) * energy3120 g xi) =
      (fun xi : ℝ => (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
        energy3120 g xi + (∑' n : ℕ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re) := by
    funext xi
    rw [sigma_eq_reciprocal_series3121, tsum_mul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [hpoint, integral_add (h0.const_mul _) hsumR, integral_const_mul]
  have hre := integral_re hsum
  change (∫ xi : ℝ, (∑' n : ℕ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re) =
    (∫ xi : ℝ, ∑' n : ℕ, reciprocal3121 n xi * (energy3120 g xi : ℂ)).re at hre
  rw [hre, hexchange, Complex.re_tsum hs]
  congr 1
  congr 1
  simpa only [mul_zero, Real.cos_zero, one_mul] using
    (square_re_eq_cosine_integral3120 g 0).symm

theorem archimedean_eq_sigma_energy3121 (g : CompactLogTest) :
    archimedeanTerm g.convolutionSquare =
      ∫ xi : ℝ, c3Sigma (2 * Real.pi * xi) * energy3120 g xi := by
  have hs : Summable (fun n : ℕ =>
      ∫ y : ℝ in Ioi 0, gammaRArchProfileTerm g.convolutionSquare n y) :=
    (summable_integralOn_norm_gammaRArchProfileTerm g.convolutionSquare).of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  rw [integral_sigma_eq_series3121]
  unfold archimedeanTerm
  rw [Complex.add_re, integralOn_archimedeanIntegrand_eq_tsum, Complex.re_tsum hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  apply tsum_congr
  exact profile_integral_re3121 g

theorem complete_gate_readback3121 (g : CompactLogTest) :
    archimedeanTerm g.convolutionSquare + finitePrimeSum g.convolutionSquare =
      ∫ xi : ℝ, (c3Sigma (2 * Real.pi * xi) +
        primeKernel3120 (globalPrimeIndexSet g.convolutionSquare) xi) * energy3120 g xi := by
  rw [archimedean_eq_sigma_energy3121, finitePrimeSum_eq_integral3120,
    ← integral_add (sigma_energy_integrable3121 g) (primeKernel_energy_integrable3120 g _)]
  congr 1
  funext xi
  ring

theorem complete_gate_integrable3121 (g : CompactLogTest) :
    Integrable (fun xi : ℝ => (c3Sigma (2 * Real.pi * xi) +
      primeKernel3120 (globalPrimeIndexSet g.convolutionSquare) xi) * energy3120 g xi) := by
  apply ((sigma_energy_integrable3121 g).add
    (primeKernel_energy_integrable3120 g (globalPrimeIndexSet g.convolutionSquare))).congr
  filter_upwards with xi
  simp only [Pi.add_apply]
  ring

theorem poweredFamily_complete_gate_readback3121
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) :
    archimedeanTerm (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare +
        finitePrimeSum (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare =
      ∫ xi : ℝ, (c3Sigma (2 * Real.pi * xi) + primeKernel3120
        (globalPrimeIndexSet (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare) xi) *
          ‖orbitMultiplier3120 rho xi - (lambda : ℂ)‖ ^ 2 *
            energy3120 (poweredFamilyOwner3117 rho N nodes n) xi := by
  rw [complete_gate_readback3121]
  apply integral_congr_ae
  filter_upwards with xi
  rw [show energy3120 (poweredFamilySpan3117 rho N nodes n lambda) xi = _ from
    fullOrbit_span_energy3120 _ rho lambda xi]
  ring

theorem poweredFamily_complete_gate_integrable3121
    (rho : ℂ) (N : ℕ) (nodes : Finset ℂ) (n : ℕ) (lambda : ℝ) :
    Integrable (fun xi : ℝ => (c3Sigma (2 * Real.pi * xi) + primeKernel3120
      (globalPrimeIndexSet (poweredFamilySpan3117 rho N nodes n lambda).convolutionSquare) xi) *
        ‖orbitMultiplier3120 rho xi - (lambda : ℂ)‖ ^ 2 *
          energy3120 (poweredFamilyOwner3117 rho N nodes n) xi) := by
  apply (complete_gate_integrable3121 (poweredFamilySpan3117 rho N nodes n lambda)).congr
  filter_upwards with xi
  rw [show energy3120 (poweredFamilySpan3117 rho N nodes n lambda) xi = _ from
    fullOrbit_span_energy3120 _ rho lambda xi]
  ring

end
end ConnesWeilRH.Source.C1RouteBArchimedeanFourierReadback3121
