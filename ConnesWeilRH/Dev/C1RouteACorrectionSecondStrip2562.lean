import ConnesWeilRH.Dev.C1RouteASignedAggregateCell2539

/-!
Correction-second strip interface. The correction channel target
`stripSecondNorm` decomposes pointwise through the already-certified weighted
aggregate `weightedPhysical2539`:

  exp(sigma*x) * ‖f'' x‖ = ‖W'' x - (2*sigma) * W' x + sigma^2 * W x‖
                          ≤ ‖W'' x‖ + 2*|sigma| * ‖W' x‖ + sigma^2 * ‖W x‖

so every per-family cell bound reuses the certified order ≤ 3 machinery of
record 2539. The three pieces are charged on the same 10240-cell production
grid: the second-jet piece through a coarse per-cell midpoint bound, the
first-jet piece through the same shape one level up, and the function piece
through the existing tight composite theorem. No numerical node table is
imported here; centers and errors stay explicit hypotheses.
-/

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

theorem externalPhysical2344_contDiff_two2562 (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    ContDiff ℝ 2 (externalPhysical2344 coefficients modulations) := by
  have hzero : weightedFunction2348 0 (externalPhysical2344 coefficients modulations)
      = externalPhysical2344 coefficients modulations := by
    funext position
    simp [weightedFunction2348, weightedExp2348]
  have hsmooth := weightedPhysical2539_contDiff 0 coefficients modulations
  rw [← hzero]
  exact hsmooth.of_le (by decide)

theorem weightedFunction2348_exp_second_jet_combo2562 (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ 2 function) (position : ℝ) :
    weightedExp2348 sigma position * deriv (deriv function) position =
      deriv (deriv (weightedFunction2348 sigma function)) position -
        ((2 : ℂ) * (sigma : ℂ)) * deriv (weightedFunction2348 sigma function) position +
        ((sigma : ℂ) ^ 2) * weightedFunction2348 sigma function position := by
  have hdW : deriv (weightedFunction2348 sigma function) position
      = weightedFirst2348 sigma function position := by
    rw [weightedFunction2348_deriv sigma function hsmooth]
  rw [weightedFunction2348_secondDerivative sigma function hsmooth position, hdW]
  simp only [weightedFirst2348, weightedFunction2348]
  ring

theorem externalPhysical2344_secondDeriv_zero_at_or_beyond_pin2562
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    {position : ℝ} (houtside : stripRadius2303 ≤ |position|) :
    deriv (deriv (externalPhysical2344 coefficients modulations)) position = 0 := by
  have hr0 : 0 ≤ stripRadius2303 := by norm_num [stripRadius2303]
  have habs : Continuous (abs : ℝ → ℝ) := continuous_abs
  have hcf : ContDiff ℝ 1 (deriv (externalPhysical2344 coefficients modulations)) :=
    ContDiff.deriv' (externalPhysical2344_contDiff_two2562 coefficients modulations)
  have hstrict : ∀ y : ℝ, stripRadius2303 < |y| →
      deriv (deriv (externalPhysical2344 coefficients modulations)) y = 0 := by
    intro y hy
    have hopen : {z : ℝ | stripRadius2303 < |z|} ∈ nhds y :=
      (habs.isOpen_preimage (Set.Ioi stripRadius2303) isOpen_Ioi).mem_nhds hy
    have hderiv : deriv (externalPhysical2344 coefficients modulations)
        =ᶠ[nhds y] 0 := by
      filter_upwards [hopen] with z (hz : stripRadius2303 < |z|)
      have hzopen : {w : ℝ | stripRadius2303 < |w|} ∈ nhds z :=
        (habs.isOpen_preimage (Set.Ioi stripRadius2303) isOpen_Ioi).mem_nhds hz
      have hzzero : externalPhysical2344 coefficients modulations =ᶠ[nhds z] 0 := by
        filter_upwards [hzopen] with w (hw : stripRadius2303 < |w|)
        exact externalPhysical2344_zero_at_or_beyond_pin2539 coefficients modulations hw.le
      have hdz := hzzero.deriv_eq
      rw [show (0 : ℝ → ℂ) = fun _ => (0 : ℂ) from rfl] at hdz ⊢
      rw [hdz, (hasDerivAt_const z (0 : ℂ)).deriv]
    have hdy := hderiv.deriv_eq
    rw [show (0 : ℝ → ℂ) = fun _ => (0 : ℂ) from rfl] at hdy
    rw [hdy, (hasDerivAt_const y (0 : ℂ)).deriv]
  by_cases hb : stripRadius2303 < |position|
  · exact hstrict position hb
  · have hrc : |position| = stripRadius2303 := le_antisymm (not_lt.mp hb) houtside
    have hcontg : Continuous
        (deriv (deriv (externalPhysical2344 coefficients modulations))) :=
      hcf.continuous_deriv (by decide)
    rcases (abs_eq hr0).mp hrc with hpos | hneg
    · rw [hpos]
      haveI : Filter.NeBot (𝓝[Set.Ioi stripRadius2303] stripRadius2303) :=
        mem_closure_iff_nhdsWithin_neBot.1
          (by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl)
      have hlim : Filter.Tendsto
          (deriv (deriv (externalPhysical2344 coefficients modulations)))
          (𝓝[Set.Ioi stripRadius2303] stripRadius2303)
          (𝓝 (deriv (deriv (externalPhysical2344 coefficients modulations))
            stripRadius2303)) :=
        hcontg.continuousAt.continuousWithinAt.tendsto
      have hconst : Filter.Tendsto (fun _ => (0 : ℂ))
          (𝓝[Set.Ioi stripRadius2303] stripRadius2303) (𝓝 (0 : ℂ)) :=
        tendsto_const_nhds
      have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝[Set.Ioi stripRadius2303] stripRadius2303]
          deriv (deriv (externalPhysical2344 coefficients modulations)) :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => by
          have hyin : stripRadius2303 < |y| := by
            have hy0 : (0 : ℝ) < y := by linarith [hr0, Set.mem_Ioi.mp hy]
            rw [abs_of_pos hy0]
            exact Set.mem_Ioi.mp hy
          exact (hstrict y hyin).symm)
      exact tendsto_nhds_unique hlim (hconst.congr' hev)
    · rw [hneg]
      haveI : Filter.NeBot (𝓝[Set.Iio (-stripRadius2303)] (-stripRadius2303)) :=
        mem_closure_iff_nhdsWithin_neBot.1
          (by rw [closure_Iio]; exact Set.mem_Iic.mpr le_rfl)
      have hlim : Filter.Tendsto
          (deriv (deriv (externalPhysical2344 coefficients modulations)))
          (𝓝[Set.Iio (-stripRadius2303)] (-stripRadius2303))
          (𝓝 (deriv (deriv (externalPhysical2344 coefficients modulations))
            (-stripRadius2303))) :=
        hcontg.continuousAt.continuousWithinAt.tendsto
      have hconst : Filter.Tendsto (fun _ => (0 : ℂ))
          (𝓝[Set.Iio (-stripRadius2303)] (-stripRadius2303)) (𝓝 (0 : ℂ)) :=
        tendsto_const_nhds
      have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝[Set.Iio (-stripRadius2303)] (-stripRadius2303)]
          deriv (deriv (externalPhysical2344 coefficients modulations)) :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => by
          have hy0 : y < 0 := by linarith [Set.mem_Iio.mp hy, hr0]
          have hyin : stripRadius2303 < |y| := by
            rw [abs_of_neg hy0]
            linarith [Set.mem_Iio.mp hy]
          exact (hstrict y hyin).symm)
      exact tendsto_nhds_unique hlim (hconst.congr' hev)

theorem externalPhysical2344_stripSecond_eq_interval2562 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    stripSecondNorm sigma (externalPhysical2344 coefficients modulations) =
      ∫ x in (-stripRadius2303)..stripRadius2303,
        Real.exp (sigma * x) *
          ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖ := by
  have hsupp : Function.support (fun x => Real.exp (sigma * x) *
      ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖) ⊆
      Set.Ioc (-stripRadius2303) stripRadius2303 := by
    intro x hx
    have hxinside : |x| < stripRadius2303 := by
      by_contra hn
      change Real.exp (sigma * x) *
        ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖ ≠ 0 at hx
      apply hx
      rw [externalPhysical2344_secondDeriv_zero_at_or_beyond_pin2562 coefficients
        modulations (not_lt.mp hn), norm_zero, mul_zero]
    exact ⟨(abs_lt.mp hxinside).1, (abs_lt.mp hxinside).2.le⟩
  unfold stripSecondNorm
  exact (intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) hsupp).symm

theorem weightedPhysical2539_secondDeriv_integrand_le2562 (sigma : ℝ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (position : ℝ) :
    Real.exp (sigma * position) *
        ‖(deriv (deriv (externalPhysical2344 coefficients modulations)) position : ℂ)‖ ≤
      ‖(iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) position : ℂ)‖ +
        (2 * |sigma|) *
          ‖(iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations)
            position : ℂ)‖ +
        sigma ^ 2 * ‖weightedPhysical2539 sigma coefficients modulations position‖ := by
  have hid := weightedFunction2348_exp_second_jet_combo2562 sigma
    (externalPhysical2344 coefficients modulations)
    (externalPhysical2344_contDiff_two2562 coefficients modulations) position
  have hexp : ‖weightedExp2348 sigma position‖ = Real.exp (sigma * position) := by
    simp only [weightedExp2348, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  calc Real.exp (sigma * position) *
      ‖(deriv (deriv (externalPhysical2344 coefficients modulations)) position : ℂ)‖
      = ‖weightedExp2348 sigma position *
          (deriv (deriv (externalPhysical2344 coefficients modulations)) position : ℂ)‖ := by
        rw [norm_mul, hexp]
    _ = ‖(deriv (deriv (weightedFunction2348 sigma
            (externalPhysical2344 coefficients modulations))) position -
          ((2 : ℂ) * (sigma : ℂ)) *
            deriv (weightedFunction2348 sigma
              (externalPhysical2344 coefficients modulations)) position +
          ((sigma : ℂ) ^ 2) * weightedFunction2348 sigma
            (externalPhysical2344 coefficients modulations) position)‖ := by
        rw [hid]
    _ ≤ ‖(deriv (deriv (weightedFunction2348 sigma
            (externalPhysical2344 coefficients modulations))) position : ℂ)‖ +
          ‖(((2 : ℂ) * (sigma : ℂ)) *
            deriv (weightedFunction2348 sigma
              (externalPhysical2344 coefficients modulations)) position : ℂ)‖ +
          ‖(((sigma : ℂ) ^ 2) * weightedFunction2348 sigma
            (externalPhysical2344 coefficients modulations) position : ℂ)‖ := by
        have hsub : ‖(deriv (deriv (weightedFunction2348 sigma
              (externalPhysical2344 coefficients modulations))) position -
            ((2 : ℂ) * (sigma : ℂ)) *
              deriv (weightedFunction2348 sigma
                (externalPhysical2344 coefficients modulations)) position : ℂ)‖ ≤
            ‖(deriv (deriv (weightedFunction2348 sigma
                (externalPhysical2344 coefficients modulations))) position : ℂ)‖ +
              ‖(((2 : ℂ) * (sigma : ℂ)) *
                deriv (weightedFunction2348 sigma
                  (externalPhysical2344 coefficients modulations)) position : ℂ)‖ :=
          norm_sub_le _ _
        exact (norm_add_le _ _).trans (add_le_add hsub le_rfl)
    _ ≤ ‖(iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations)
            position : ℂ)‖ +
          (2 * |sigma|) *
            ‖(iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations)
              position : ℂ)‖ +
          sigma ^ 2 * ‖weightedPhysical2539 sigma coefficients modulations position‖ := by
        simp only [weightedPhysical2539, iteratedDeriv_succ, iteratedDeriv_zero,
          norm_mul, norm_pow, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
          sq_abs]
        exact le_refl _

theorem weightedPhysical2539_first_le_signed_midpoint2562 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    {a b : ℝ} (hab : a ≤ b) : ∀ x ∈ Set.Icc a b,
    ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖ ≤
      signedJetUpper2539 1 sigma centers errors modulations ((a + b) / 2) +
        signedCurvatureUpper2539 sigma centers errors modulations a b * ((b - a) / 2) := by
  let f := weightedPhysical2539 sigma coefficients modulations
  let L := signedCurvatureUpper2539 sigma centers errors modulations a b
  have hsecond : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 2 f x‖ ≤ L :=
    weightedPhysical2539_second_le_signed_midpoint sigma coefficients centers errors
      modulations herror hab
  have hL : 0 ≤ L := (norm_nonneg _).trans (hsecond a ⟨le_rfl, hab⟩)
  have hd : Differentiable ℝ (iteratedDeriv 1 f) :=
    ContDiff.differentiable_iteratedDeriv' 1
      (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
        (by decide))
  have hmid : (a + b) / 2 ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  intro x hx
  have hvariation := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hd x)
    (fun x hx => by simpa only [← iteratedDeriv_succ] using hsecond x hx)
    (convex_Icc a b) hmid hx
  have hdist : |x - (a + b) / 2| ≤ (b - a) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hvariation' : ‖iteratedDeriv 1 f x - iteratedDeriv 1 f ((a + b) / 2)‖ ≤
      L * |x - (a + b) / 2| := by
    simpa only [Real.norm_eq_abs] using hvariation
  have hvar : ‖iteratedDeriv 1 f x - iteratedDeriv 1 f ((a + b) / 2)‖ ≤
      L * ((b - a) / 2) := hvariation'.trans (mul_le_mul_of_nonneg_left hdist hL)
  have hcenter := weightedPhysical2539_jet_le_center_error 1 sigma coefficients centers
    errors modulations herror ((a + b) / 2)
  change ‖iteratedDeriv 1 f x‖ ≤ _
  calc
    _ = ‖iteratedDeriv 1 f ((a + b) / 2) +
        (iteratedDeriv 1 f x - iteratedDeriv 1 f ((a + b) / 2))‖ := by congr 1; abel
    _ ≤ ‖iteratedDeriv 1 f ((a + b) / 2)‖ +
        ‖iteratedDeriv 1 f x - iteratedDeriv 1 f ((a + b) / 2)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hcenter hvar

noncomputable def signedFirstCompositeUpper2562 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (left step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells, step *
    (signedJetUpper2539 1 sigma centers errors modulations
        (left + ((index : ℝ) + 1 / 2) * step) +
      signedCurvatureUpper2539 sigma centers errors modulations
        (left + (index : ℝ) * step) (left + ((index : ℝ) + 1) * step) * (step / 2))

noncomputable def signedSecondCompositeUpper2562 (sigma : ℝ)
    (centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (left step : ℝ) (cells : ℕ) : ℝ :=
  ∑ index ∈ Finset.range cells, step *
    signedCurvatureUpper2539 sigma centers errors modulations
      (left + (index : ℝ) * step) (left + ((index : ℝ) + 1) * step)

theorem weightedPhysical2539_first_integral_le_composite2562 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    (left step : ℝ) (cells : ℕ) (hstep : 0 < step) :
    (∫ x in left..(left + cells * step),
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) ≤
      signedFirstCompositeUpper2562 sigma centers errors modulations left step cells := by
  have hcont := (ContDiff.differentiable_iteratedDeriv' 1
    (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
      (by decide))).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
    (μ := volume) (a := fun index : ℕ => left + (index : ℝ) * step) (n := cells)
    (fun (index : ℕ) _ => hcont.intervalIntegrable
      (left + (index : ℝ) * step) (left + ((index + 1 : ℕ) : ℝ) * step))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] at hsum
  rw [← hsum]
  unfold signedFirstCompositeUpper2562
  apply Finset.sum_le_sum
  intro index _
  have horder : left + (index : ℝ) * step < left + ((index : ℝ) + 1) * step := by linarith
  have hwidth : (left + ((index : ℝ) + 1) * step) - (left + (index : ℝ) * step) = step := by
    ring
  have hmid : (left + (index : ℝ) * step + (left + ((index : ℝ) + 1) * step)) / 2
      = left + ((index : ℝ) + 1 / 2) * step := by field_simp; ring
  have hpoint := weightedPhysical2539_first_le_signed_midpoint2562 sigma coefficients
    centers errors modulations herror (a := left + (index : ℝ) * step)
    (b := left + ((index : ℝ) + 1) * step) (le_of_lt horder)
  have hconst := intervalIntegral.integral_mono_on (le_of_lt horder)
    (hcont.intervalIntegrable _ _)
    (intervalIntegral.intervalIntegrable_const (μ := volume)
      (a := left + (index : ℝ) * step) (b := left + ((index : ℝ) + 1) * step))
    hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul, hwidth, hmid] at hconst
  exact hconst

theorem weightedPhysical2539_second_integral_le_composite2562 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index)
    (left step : ℝ) (cells : ℕ) (hstep : 0 < step) :
    (∫ x in left..(left + cells * step),
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖) ≤
      signedSecondCompositeUpper2562 sigma centers errors modulations left step cells := by
  have hcont := (ContDiff.differentiable_iteratedDeriv' 2
    (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
      (by decide))).continuous.norm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖)
    (μ := volume) (a := fun index : ℕ => left + (index : ℝ) * step) (n := cells)
    (fun (index : ℕ) _ => hcont.intervalIntegrable
      (left + (index : ℝ) * step) (left + ((index + 1 : ℕ) : ℝ) * step))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, add_zero] at hsum
  rw [← hsum]
  unfold signedSecondCompositeUpper2562
  apply Finset.sum_le_sum
  intro index _
  have horder : left + (index : ℝ) * step < left + ((index : ℝ) + 1) * step := by linarith
  have hwidth : (left + ((index : ℝ) + 1) * step) - (left + (index : ℝ) * step) = step := by
    ring
  have hpoint := weightedPhysical2539_second_le_signed_midpoint sigma coefficients
    centers errors modulations herror (le_of_lt horder)
  have hconst := intervalIntegral.integral_mono_on (le_of_lt horder)
    (hcont.intervalIntegrable _ _)
    (intervalIntegral.intervalIntegrable_const (μ := volume)
      (a := left + (index : ℝ) * step) (b := left + ((index : ℝ) + 1) * step))
    (fun x hx => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hpoint x hx)
  simp only [intervalIntegral.integral_const, smul_eq_mul, hwidth] at hconst
  exact hconst

theorem externalPhysical2344_stripSecond_le_decomposed2562 (sigma : ℝ)
    (coefficients centers : Fin 30 → ℂ) (errors modulations : Fin 30 → ℝ)
    (herror : ∀ index, ‖coefficients index - centers index‖ ≤ errors index) :
    stripSecondNorm sigma (externalPhysical2344 coefficients modulations) ≤
      signedSecondCompositeUpper2562 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 +
      2 * |sigma| * signedFirstCompositeUpper2562 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 +
      sigma ^ 2 * signedCompositeUpper2539 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
  rw [externalPhysical2344_stripSecond_eq_interval2562 sigma coefficients modulations]
  have hstep : 0 < 2 * stripRadius2303 / 10240 := by norm_num [stripRadius2303]
  have hab : (-stripRadius2303 : ℝ) ≤ stripRadius2303 := by linarith [hstep]
  have hgrid : (-stripRadius2303 : ℝ) + (10240 : ℝ) * (2 * stripRadius2303 / 10240)
      = stripRadius2303 := by ring
  have hcf : ContDiff ℝ 1
      (deriv (externalPhysical2344 coefficients modulations)) :=
    ContDiff.deriv' (externalPhysical2344_contDiff_two2562 coefficients modulations)
  have hc2 : Continuous
      (deriv (deriv (externalPhysical2344 coefficients modulations))) :=
    hcf.continuous_deriv (by decide)
  have hexpcont : Continuous fun x : ℝ => Real.exp (sigma * x) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hI2 : IntervalIntegrable (fun x =>
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (ContDiff.differentiable_iteratedDeriv' 2
      (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
        (by decide))).continuous.norm.intervalIntegrable _ _
  have hI1 : IntervalIntegrable (fun x =>
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (ContDiff.differentiable_iteratedDeriv' 1
      (weightedPhysical2539_contDiff sigma coefficients modulations |>.of_le
        (by decide))).continuous.norm.intervalIntegrable _ _
  have hI0 : IntervalIntegrable (fun x =>
      ‖weightedPhysical2539 sigma coefficients modulations x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (weightedPhysical2539_contDiff sigma coefficients modulations).continuous.norm
      |>.intervalIntegrable _ _
  have hleft : IntervalIntegrable (fun x => Real.exp (sigma * x) *
      ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖)
      volume (-stripRadius2303) stripRadius2303 :=
    (hexpcont.mul hc2.norm).intervalIntegrable _ _
  have hI1c : IntervalIntegrable (fun x => (2 * |sigma|) *
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
      volume (-stripRadius2303) stripRadius2303 := hI1.const_mul _
  have hI0c : IntervalIntegrable (fun x => (sigma ^ 2) *
      ‖weightedPhysical2539 sigma coefficients modulations x‖)
      volume (-stripRadius2303) stripRadius2303 := hI0.const_mul _
  have hsplit : (∫ x in (-stripRadius2303)..stripRadius2303, Real.exp (sigma * x) *
        ‖deriv (deriv (externalPhysical2344 coefficients modulations)) x‖) ≤
      ∫ x in (-stripRadius2303)..stripRadius2303,
        ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖ +
          (2 * |sigma|) *
            ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖ +
          sigma ^ 2 * ‖weightedPhysical2539 sigma coefficients modulations x‖ := by
    refine intervalIntegral.integral_mono_on hab hleft ((hI2.add hI1c).add hI0c) ?_
    intro x _
    exact weightedPhysical2539_secondDeriv_integrand_le2562 sigma coefficients
      modulations x
  refine hsplit.trans ?_
  have e2a : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖ +
      (2 * |sigma|) *
        ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖ +
      sigma ^ 2 * ‖weightedPhysical2539 sigma coefficients modulations x‖) =
      ((∫ x in (-stripRadius2303)..stripRadius2303,
          ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖) +
        (∫ x in (-stripRadius2303)..stripRadius2303, (2 * |sigma|) *
          ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)) +
      (∫ x in (-stripRadius2303)..stripRadius2303, (sigma ^ 2) *
        ‖weightedPhysical2539 sigma coefficients modulations x‖) := by
    rw [intervalIntegral.integral_add (hI2.add hI1c) hI0c,
      intervalIntegral.integral_add hI2 hI1c]
  have e2b : (∫ x in (-stripRadius2303)..stripRadius2303, (2 * |sigma|) *
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) =
      (2 * |sigma|) * (∫ x in (-stripRadius2303)..stripRadius2303,
        ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) :=
    intervalIntegral.integral_const_mul (2 * |sigma|)
      (fun x => ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖)
  have e2c : (∫ x in (-stripRadius2303)..stripRadius2303, (sigma ^ 2) *
      ‖weightedPhysical2539 sigma coefficients modulations x‖) =
      (sigma ^ 2) * (∫ x in (-stripRadius2303)..stripRadius2303,
        ‖weightedPhysical2539 sigma coefficients modulations x‖) :=
    intervalIntegral.integral_const_mul (sigma ^ 2)
      (fun x => ‖weightedPhysical2539 sigma coefficients modulations x‖)
  rw [e2a, e2b, e2c]
  have t1 := weightedPhysical2539_second_integral_le_composite2562 sigma coefficients
    centers errors modulations herror (-stripRadius2303)
    (2 * stripRadius2303 / 10240) 10240 hstep
  have t2 := weightedPhysical2539_first_integral_le_composite2562 sigma coefficients
    centers errors modulations herror (-stripRadius2303)
    (2 * stripRadius2303 / 10240) 10240 hstep
  have t3 := weightedPhysical2539_norm_integral_le_signed_composite sigma coefficients
    centers errors modulations herror (-stripRadius2303)
    (2 * stripRadius2303 / 10240) 10240 hstep
  have t1' : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖iteratedDeriv 2 (weightedPhysical2539 sigma coefficients modulations) x‖) ≤
      signedSecondCompositeUpper2562 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
    simpa only [Nat.cast_ofNat, hgrid] using t1
  have t2' : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖iteratedDeriv 1 (weightedPhysical2539 sigma coefficients modulations) x‖) ≤
      signedFirstCompositeUpper2562 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
    simpa only [Nat.cast_ofNat, hgrid] using t2
  have t3' : (∫ x in (-stripRadius2303)..stripRadius2303,
      ‖weightedPhysical2539 sigma coefficients modulations x‖) ≤
      signedCompositeUpper2539 sigma centers errors modulations
        (-stripRadius2303) (2 * stripRadius2303 / 10240) 10240 := by
    simpa only [Nat.cast_ofNat, hgrid] using t3
  exact add_le_add
    (add_le_add t1' (mul_le_mul_of_nonneg_left t2' (mul_nonneg zero_le_two (abs_nonneg sigma))))
    (mul_le_mul_of_nonneg_left t3' (pow_two_nonneg sigma))

end ConnesWeilRH.Dev
