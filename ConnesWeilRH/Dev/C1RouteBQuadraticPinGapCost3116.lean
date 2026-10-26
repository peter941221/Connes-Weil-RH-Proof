import ConnesWeilRH.Dev.C1DetectorNearCollisionCost3096
import ConnesWeilRH.Dev.C1ExplicitHealthyCorrectionBudget
import ConnesWeilRH.Dev.C1StripTransport2722C
import ConnesWeilRH.Dev.C1FourPointRowBWired2721
import Mathlib.Analysis.Complex.Schwarz

/-! Necessary near-line cost of the actual correction's quadratic strip pin.

The entire transform takes opposite unit values at rho and 1-conj(rho).
Schwarz's disk estimate turns the quadratic strip pin into a quantitative
height/gap cost. This does not assert the existence of off-line zeros or
supply a pin, gate, or RH proof.
-/

namespace ConnesWeilRH.Source.C1RouteBQuadraticPinGapCost3116

open CC20YoshidaConvolution.CompactLogTest
open C1ExplicitSmoothSeed C1ExplicitFiniteNodeCorrection
open C1ExplicitHealthyCorrectionBudget C1HealthyYoshidaUnscaledOrbit
open C1StripTransport2722C C1FourPointRowBWired2721

noncomputable section

def quadraticStripPin3116 (F : ℂ → ℂ) (C2 : ℝ) : Prop :=
  ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
    ‖t / (2 * Real.pi)‖ ^ 2 * ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C2

theorem analytic_opposite_targets_quadratic_cost3116
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (rho : ℂ) (C : ℝ)
    (hpin : ∀ w : ℂ, w.re ∈ Set.Icc (0 : ℝ) 1 → w.im ^ 2 * ‖F w‖ ≤ C)
    (hone : F rho = 1) (hminus : F (1 - star rho) = -1)
    (hgap : |rho.re - 1 / 2| ≤ 1 / 16) (hheight : 1 ≤ |rho.im|) :
    rho.im ^ 2 ≤ (16 * C + 4 * rho.im ^ 2) * |rho.re - 1 / 2| := by
  let c : ℂ := 1 - star rho
  let δ : ℝ := |rho.re - 1 / 2|
  let M : ℝ := 4 * C / rho.im ^ 2
  have hcre : c.re = 1 - rho.re := by simp [c]
  have hcim : c.im = rho.im := by simp [c]
  have hsq : 0 < rho.im ^ 2 := by
    apply sq_pos_of_ne_zero
    intro hz
    norm_num [hz] at hheight
  have hbound (w : ℂ) (hw : w ∈ Metric.ball c (1 / 4 : ℝ)) : ‖F w‖ ≤ M := by
    have hn : ‖w - c‖ < (1 / 4 : ℝ) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hre : |w.re - (1 - rho.re)| < (1 / 4 : ℝ) := by
      simpa only [Complex.sub_re, hcre] using
        (Complex.abs_re_le_norm (w - c)).trans_lt hn
    have him : |w.im - rho.im| < (1 / 4 : ℝ) := by
      simpa only [Complex.sub_im, hcim] using
        (Complex.abs_im_le_norm (w - c)).trans_lt hn
    have hwstrip : w.re ∈ Set.Icc (0 : ℝ) 1 := by
      have hg := abs_le.mp hgap
      have hr := abs_lt.mp hre
      constructor <;> linarith
    have htri : |rho.im| ≤ |w.im - rho.im| + |w.im| := by
      calc |rho.im| = |(rho.im - w.im) + w.im| := by congr 1; ring
           _ ≤ |rho.im - w.im| + |w.im| := abs_add_le _ _
           _ = _ := by rw [abs_sub_comm rho.im w.im]
    have himlo : |rho.im| / 2 ≤ |w.im| := by linarith
    have hweight : rho.im ^ 2 / 4 ≤ w.im ^ 2 := by
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ |rho.im| / 2) himlo 2
      norm_num [div_pow, sq_abs] at hp
      exact hp
    have hlocal := (mul_le_mul_of_nonneg_right hweight (norm_nonneg (F w))).trans
      (hpin w hwstrip)
    apply (le_div_iff₀ hsq).mpr
    nlinarith
  have hFc : F c = -1 := hminus
  have hmaps : Set.MapsTo F (Metric.ball c (1 / 4 : ℝ))
      (Metric.closedBall (F c) (M + 1)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖F w - F c‖ ≤ ‖F w‖ + ‖F c‖ := norm_sub_le _ _
         _ ≤ M + 1 := by rw [hFc]; simpa using hbound w hw
  have hdiff : rho - c = ((2 * (rho.re - 1 / 2) : ℝ) : ℂ) := by
    dsimp [c]
    apply Complex.ext
    · simp
      ring
    · simp
  have hdist : dist rho c = 2 * δ := by
    rw [dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num [δ]
  have hrho : rho ∈ Metric.ball c (1 / 4 : ℝ) := by
    rw [Metric.mem_ball, hdist]
    dsimp [δ]
    linarith
  have htarg : dist (F rho) (F c) = (2 : ℝ) := by
    rw [hone, hFc]
    norm_num [dist_eq_norm]
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    hF.differentiableOn hmaps hrho
  rw [htarg, hdist] at hschwarz
  have hunit : 1 ≤ 4 * (M + 1) * δ := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hunit hsq.le
  calc rho.im ^ 2 ≤ (4 * (M + 1) * δ) * rho.im ^ 2 := by simpa using hscaled
       _ = (16 * C + 4 * rho.im ^ 2) * |rho.re - 1 / 2| := by
         have hne : rho.im ≠ 0 := by intro hz; simp [hz] at hsq
         dsimp [M, δ]
         field_simp [hne]
         ring

theorem quadratic_pin_im_square3116 {F : ℂ → ℂ} {C2 : ℝ}
    (hpin : quadraticStripPin3116 F C2) (w : ℂ)
    (hw : w.re ∈ Set.Icc (0 : ℝ) 1) :
    w.im ^ 2 * ‖F w‖ ≤ (2 * Real.pi) ^ 2 * C2 := by
  have h := hpin w.re hw w.im
  rw [Complex.re_add_im] at h
  have hden : (2 * Real.pi) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hwgt : ‖w.im / (2 * Real.pi)‖ ^ 2 = w.im ^ 2 / (2 * Real.pi) ^ 2 := by
    rw [Real.norm_eq_abs, abs_div, div_pow, sq_abs, sq_abs]
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (2 * Real.pi))
  rw [hwgt] at hmul
  have heq : (2 * Real.pi) ^ 2 * (w.im ^ 2 / (2 * Real.pi) ^ 2 * ‖F w‖) =
      w.im ^ 2 * ‖F w‖ := by field_simp
  rwa [heq] at hmul

theorem quadratic_pin_gap_cost3116 (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (rho : ℂ) (C2 : ℝ) (hpin : quadraticStripPin3116 F C2)
    (hone : F rho = 1) (hminus : F (1 - star rho) = -1)
    (hgap : |rho.re - 1 / 2| ≤ 1 / 16) (hheight : 1 ≤ |rho.im|) :
    rho.im ^ 2 ≤ (16 * ((2 * Real.pi) ^ 2 * C2) + 4 * rho.im ^ 2) *
      |rho.re - 1 / 2| := by
  exact analytic_opposite_targets_quadratic_cost3116 F hF rho _
    (quadratic_pin_im_square3116 hpin) hone hminus hgap hheight

theorem powered_correction_pin_gap_cost3116
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (C2 : ℝ)
    (hoff : rho.re ≠ 1 / 2)
    (hgap : |rho.re - 1 / 2| ≤ 1 / 16) (hheight : 1 ≤ |rho.im|)
    (hpin : quadraticStripPin3116
      (laplaceAt (explicitPoweredHealthyCorrection rho N routeNodes)) C2) :
    rho.im ^ 2 ≤ (16 * ((2 * Real.pi) ^ 2 * C2) + 4 * rho.im ^ 2) *
      |rho.re - 1 / 2| := by
  apply quadratic_pin_gap_cost3116 _
    (C1XiResidue.differentiable_laplaceAt _) rho C2 hpin
  · simpa only [healthyUnscaledTargetValue_rho] using
      explicitPoweredHealthyCorrection_targets rho N routeNodes
        ⟨rho, mem_healthyUnscaledTargetNodes_rho rho⟩
  · exact (explicitPoweredHealthyCorrection_targets rho N routeNodes
      ⟨1 - star rho, mem_healthyUnscaledTargetNodes_companion rho⟩).trans
        (healthyUnscaledTargetValue_companion rho hoff)
  · exact hgap
  · exact hheight

theorem powered_correction_cardinal_pin_cost3116
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (C2 : ℝ)
    (hoff : rho.re ≠ 1 / 2)
    (hgap : |rho.re - 1 / 2| ≤ 1 / 16) (hheight : 1 ≤ |rho.im|)
    (hpin : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖t / (2 * Real.pi)‖ ^ 2 *
        ‖cardinalSum (healthyCorrectionNodes rho N routeNodes) poweredSeed
          (healthyCorrectionValue rho) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C2) :
    rho.im ^ 2 ≤ (16 * ((2 * Real.pi) ^ 2 * C2) + 4 * rho.im ^ 2) *
      |rho.re - 1 / 2| := by
  apply powered_correction_pin_gap_cost3116 rho N routeNodes C2 hoff hgap hheight
  intro σ hσ t
  simpa only [explicitPoweredHealthyCorrection, laplaceAt_correction, cardinalSum]
    using hpin σ hσ t

theorem powered_correction_fixed_pin_gap_floor3116
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (hoff : rho.re ≠ 1 / 2)
    (hheight : 1 ≤ |rho.im|)
    (hpin : quadraticStripPin3116
      (laplaceAt (explicitPoweredHealthyCorrection rho N routeNodes)) wiredC2RowB2721) :
    (1 : ℝ) / 29696000004 ≤ |rho.re - 1 / 2| := by
  by_cases hgap : |rho.re - 1 / 2| ≤ 1 / 16
  · have hcost := powered_correction_pin_gap_cost3116 rho N routeNodes
      wiredC2RowB2721 hoff hgap hheight hpin
    have hheightSq : (1 : ℝ) ≤ rho.im ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hheight 2
      simpa only [one_pow, sq_abs] using h
    have hrest : 0 ≤ (rho.im ^ 2 - 1) * (1 - 4 * |rho.re - 1 / 2|) :=
      mul_nonneg (by linarith) (by linarith)
    have hunit : 1 ≤ (16 * ((2 * Real.pi) ^ 2 * wiredC2RowB2721) + 4) *
        |rho.re - 1 / 2| := by nlinarith
    have hpi : (2 * Real.pi) ^ 2 ≤ (64 : ℝ) := by
      have hp : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
      calc (2 * Real.pi) ^ 2 ≤ (8 : ℝ) ^ 2 :=
             pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.pi) hp 2
           _ = 64 := by norm_num
    have hC := mul_le_mul_of_nonneg_right hpi
      (by norm_num [wiredC2RowB2721] : 0 ≤ wiredC2RowB2721)
    have hpriced : 1 ≤ (29696000004 : ℝ) * |rho.re - 1 / 2| := by
      refine hunit.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      norm_num [wiredC2RowB2721] at hC ⊢
      linarith
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 29696000004)).mpr
    nlinarith
  · exact (by norm_num : (1 : ℝ) / 29696000004 ≤ 1 / 16).trans (not_le.mp hgap).le

theorem reject_fixed_pin_below_gap_floor3116
    (rho : ℂ) (N : ℕ) (routeNodes : Finset ℂ) (hoff : rho.re ≠ 1 / 2)
    (hheight : 1 ≤ |rho.im|)
    (hsmall : |rho.re - 1 / 2| < (1 : ℝ) / 29696000004)
    (hpin : quadraticStripPin3116
      (laplaceAt (explicitPoweredHealthyCorrection rho N routeNodes)) wiredC2RowB2721) :
    False := by
  exact (not_lt_of_ge
    (powered_correction_fixed_pin_gap_floor3116 rho N routeNodes hoff hheight hpin)) hsmall

def tinyGapPoint3116 : ℂ :=
  (((1 / 2 : ℝ) + 1 / 10 ^ 12 : ℝ) : ℂ) + Complex.I

/-- An exact interpolation counterexample to a fixed cap over all parameters.
It is a specified complex point, not a claim about a zeta zero. -/
theorem tiny_gap_correction_rejects_fixed_pin3116 (N : ℕ) (routeNodes : Finset ℂ) :
    ¬quadraticStripPin3116
      (laplaceAt (explicitPoweredHealthyCorrection tinyGapPoint3116 N routeNodes))
      wiredC2RowB2721 := by
  intro hpin
  exact reject_fixed_pin_below_gap_floor3116 tinyGapPoint3116 N routeNodes
    (by norm_num [tinyGapPoint3116]) (by norm_num [tinyGapPoint3116])
    (by norm_num [tinyGapPoint3116]) hpin

end
end ConnesWeilRH.Source.C1RouteBQuadraticPinGapCost3116
