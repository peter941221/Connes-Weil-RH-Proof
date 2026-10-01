import ConnesWeilRH.Dev.C1RouteAChordPanel

namespace ConnesWeilRH.Dev

open scoped ContDiff
open MeasureTheory
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def weightedExp2348 (sigma position : ℝ) : ℂ :=
  (Real.exp (sigma * position) : ℝ)

noncomputable def weightedFunction2348 (sigma : ℝ) (function : ℝ → ℂ) (position : ℝ) : ℂ :=
  weightedExp2348 sigma position * function position

noncomputable def weightedFirst2348 (sigma : ℝ) (function : ℝ → ℂ) (position : ℝ) : ℂ :=
  weightedExp2348 sigma position * ((sigma : ℂ) * function position + deriv function position)

noncomputable def weightedCurvature2348 (sigma radius zeroBound firstBound secondBound : ℝ) : ℝ :=
  Real.exp (|sigma| * radius) * (secondBound + 2 * |sigma| * firstBound + sigma ^ 2 * zeroBound)

theorem weightedExp2348_hasDerivAt (sigma position : ℝ) :
    HasDerivAt (weightedExp2348 sigma) (weightedExp2348 sigma position * (sigma : ℂ)) position := by
  simpa only [weightedExp2348, mul_one, Complex.ofReal_mul] using
    (((hasDerivAt_id position).const_mul sigma).exp).ofReal_comp

theorem weightedFunction2348_contDiff (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function) :
    ContDiff ℝ (2 : ℕ∞ω) (weightedFunction2348 sigma function) := by
  have hexp : ContDiff ℝ (2 : ℕ∞ω) (fun position : ℝ => Real.exp (sigma * position)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  exact (Complex.ofRealCLM.contDiff.comp hexp).mul hsmooth

theorem weightedFunction2348_deriv (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function) :
    deriv (weightedFunction2348 sigma function) = weightedFirst2348 sigma function := by
  funext position
  have hfunction := (hsmooth.differentiable (by decide) position).hasDerivAt
  convert ((weightedExp2348_hasDerivAt sigma position).mul hfunction).deriv using 1
  dsimp [weightedFunction2348, weightedFirst2348]
  ring

theorem weightedFunction2348_secondDerivative (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function) (position : ℝ) :
    deriv (deriv (weightedFunction2348 sigma function)) position =
      weightedExp2348 sigma position * (deriv (deriv function) position +
        2 * (sigma : ℂ) * deriv function position + (sigma : ℂ) ^ 2 * function position) := by
  rw [weightedFunction2348_deriv sigma function hsmooth]
  have hsmoothFirst : ContDiff ℝ (1 : ℕ∞ω) (deriv function) := ContDiff.deriv' hsmooth
  have hfunction := (hsmooth.differentiable (by decide) position).hasDerivAt
  have hfirst := (hsmoothFirst.differentiable (by decide) position).hasDerivAt
  have hfactor := (hfunction.const_mul (sigma : ℂ)).add hfirst
  convert ((weightedExp2348_hasDerivAt sigma position).mul hfactor).deriv using 1
  dsimp [weightedFirst2348]
  ring

theorem weightedFunction2348_norm (sigma : ℝ) (function : ℝ → ℂ) (position : ℝ) :
    ‖weightedFunction2348 sigma function position‖ =
      Real.exp (sigma * position) * ‖function position‖ := by
  simp only [weightedFunction2348, weightedExp2348, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem weightedFunction2348_curvature_bound (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    (radius position zeroBound firstBound secondBound : ℝ) (hposition : |position| ≤ radius)
    (hzero : ‖function position‖ ≤ zeroBound)
    (hfirst : ‖deriv function position‖ ≤ firstBound)
    (hsecond : ‖deriv (deriv function) position‖ ≤ secondBound) :
    ‖deriv (deriv (weightedFunction2348 sigma function)) position‖ ≤
      weightedCurvature2348 sigma radius zeroBound firstBound secondBound := by
  rw [weightedFunction2348_secondDerivative sigma function hsmooth position, norm_mul]
  have hexpNorm : ‖weightedExp2348 sigma position‖ = Real.exp (sigma * position) := by
    simp only [weightedExp2348, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hexpNorm]
  have hphase : sigma * position ≤ |sigma| * radius := by
    calc sigma * position ≤ |sigma * position| := le_abs_self _
         _ = |sigma| * |position| := abs_mul _ _
         _ ≤ |sigma| * radius := mul_le_mul_of_nonneg_left hposition (abs_nonneg sigma)
  have hnormFirst : ‖2 * (sigma : ℂ) * deriv function position‖ ≤ 2 * |sigma| * firstBound := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num) (abs_nonneg sigma))
  have hnormZero : ‖(sigma : ℂ) ^ 2 * function position‖ ≤ sigma ^ 2 * zeroBound := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left hzero (sq_nonneg sigma)
  have hnorm : ‖deriv (deriv function) position + 2 * (sigma : ℂ) * deriv function position +
      (sigma : ℂ) ^ 2 * function position‖ ≤
      secondBound + 2 * |sigma| * firstBound + sigma ^ 2 * zeroBound :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hsecond hnormFirst)) hnormZero)
  unfold weightedCurvature2348
  exact mul_le_mul (Real.exp_le_exp.mpr hphase) hnorm
    (norm_nonneg _) (Real.exp_nonneg _)

theorem weightedStripNorm2348_eq_interval (sigma : ℝ) (function : ℝ → ℂ)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hsupport : Function.support function ⊆ Set.Icc (-radius) radius) :
    stripNorm sigma function = ∫ position in (-radius)..radius,
      ‖weightedFunction2348 sigma function position‖ := by
  have hset : (∫ position in Set.Icc (-radius) radius,
      Real.exp (sigma * position) * ‖function position‖) = stripNorm sigma function := by
    unfold stripNorm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro position hposition
    have hzero : function position = 0 := by
      by_contra hnonzero
      exact hposition (hsupport hnonzero)
    simp [hzero]
  rw [← hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -radius ≤ radius)]
  apply intervalIntegral.integral_congr
  intro position _
  exact (weightedFunction2348_norm sigma function position).symm

theorem stripNorm_le_nodeUpper2348 (sigma : ℝ) (function : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (2 : ℕ∞ω) function)
    (radius step zeroBound firstBound secondBound : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ)
    (hradius : 0 ≤ radius) (hstep : 0 < step) (hgrid : (cells : ℝ) * step = 2 * radius)
    (hsupport : Function.support function ⊆ Set.Icc (-radius) radius)
    (hzero : ∀ position ∈ Set.Icc (-radius) radius, ‖function position‖ ≤ zeroBound)
    (hfirst : ∀ position ∈ Set.Icc (-radius) radius, ‖deriv function position‖ ≤ firstBound)
    (hsecond : ∀ position ∈ Set.Icc (-radius) radius,
      ‖deriv (deriv function) position‖ ≤ secondBound)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-radius + index * step)) * ‖function (-radius + index * step)‖ ≤
        nodeUpper index) :
    stripNorm sigma function ≤ compositeNodeUpper2347 nodeUpper step cells +
      step ^ 2 * (2 * radius) *
        weightedCurvature2348 sigma radius zeroBound firstBound secondBound / 12 := by
  have hend : -radius + (cells : ℝ) * step = radius := by rw [hgrid]; ring
  have hcurve : ∀ position ∈ Set.Icc (-radius) (-radius + cells * step),
      ‖deriv (deriv (weightedFunction2348 sigma function)) position‖ ≤
        weightedCurvature2348 sigma radius zeroBound firstBound secondBound := by
    intro position hposition
    rw [hend] at hposition
    exact weightedFunction2348_curvature_bound sigma function hsmooth radius position
      zeroBound firstBound secondBound (abs_le.mpr hposition)
      (hzero position hposition) (hfirst position hposition) (hsecond position hposition)
  have hnodeWeighted : ∀ index ≤ cells,
      ‖weightedFunction2348 sigma function (-radius + index * step)‖ ≤ nodeUpper index := by
    intro index hindex
    rw [weightedFunction2348_norm]
    exact hnodes index hindex
  have h := normIntegralCompositeUpper_of_nodeBounds2347 (weightedFunction2348 sigma function)
    (weightedFunction2348_contDiff sigma function hsmooth) (-radius) step
    (weightedCurvature2348 sigma radius zeroBound firstBound secondBound) cells nodeUpper
    hstep hcurve hnodeWeighted
  rw [weightedStripNorm2348_eq_interval sigma function radius hradius hsupport]
  rw [hend, hgrid] at h
  exact h

theorem correctedPhysical_stripNorm_le_nodeUpper2348
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma step zeroBound firstBound secondBound : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ)
    (hstep : 0 < step) (hgrid : (cells : ℝ) * step = 2 * storedWidth 4 ^ 2)
    (hzero : ∀ position ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖correctedPhysical coefficients modulations position‖ ≤ zeroBound)
    (hfirst : ∀ position ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖deriv (correctedPhysical coefficients modulations) position‖ ≤ firstBound)
    (hsecond : ∀ position ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖deriv (deriv (correctedPhysical coefficients modulations)) position‖ ≤ secondBound)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
        ‖correctedPhysical coefficients modulations (-(storedWidth 4 ^ 2) + index * step)‖ ≤
          nodeUpper index) :
    stripNorm sigma (correctedPhysical coefficients modulations) ≤
      compositeNodeUpper2347 nodeUpper step cells + step ^ 2 * (2 * storedWidth 4 ^ 2) *
        weightedCurvature2348 sigma (storedWidth 4 ^ 2) zeroBound firstBound secondBound / 12 := by
  exact stripNorm_le_nodeUpper2348 sigma (correctedPhysical coefficients modulations)
    ((correctedPhysical_contDiff coefficients modulations).of_le (by decide : (2 : ℕ∞ω) ≤ ∞))
    (storedWidth 4 ^ 2) step zeroBound firstBound secondBound cells nodeUpper (sq_nonneg _)
    hstep hgrid ((subset_tsupport _).trans
      (correctedPhysical_tsupport_subset_four coefficients modulations)) hzero hfirst hsecond hnodes

theorem correctedPhysical_stripSecondNorm_le_nodeUpper2348
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma step zeroBound firstBound secondBound : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ)
    (hstep : 0 < step) (hgrid : (cells : ℝ) * step = 2 * storedWidth 4 ^ 2)
    (hzero : ∀ position ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖deriv (deriv (correctedPhysical coefficients modulations)) position‖ ≤ zeroBound)
    (hfirst : ∀ position ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖deriv (deriv (deriv (correctedPhysical coefficients modulations))) position‖ ≤ firstBound)
    (hsecond : ∀ position ∈ Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2),
      ‖deriv (deriv (deriv (deriv (correctedPhysical coefficients modulations)))) position‖ ≤
        secondBound)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
        ‖deriv (deriv (correctedPhysical coefficients modulations))
          (-(storedWidth 4 ^ 2) + index * step)‖ ≤ nodeUpper index) :
    stripSecondNorm sigma (correctedPhysical coefficients modulations) ≤
      compositeNodeUpper2347 nodeUpper step cells + step ^ 2 * (2 * storedWidth 4 ^ 2) *
        weightedCurvature2348 sigma (storedWidth 4 ^ 2) zeroBound firstBound secondBound / 12 := by
  have hsmooth : ContDiff ℝ (4 : ℕ∞ω) (correctedPhysical coefficients modulations) :=
    (correctedPhysical_contDiff coefficients modulations).of_le (by decide : (4 : ℕ∞ω) ≤ ∞)
  have hsmoothFirst : ContDiff ℝ (3 : ℕ∞ω) (deriv (correctedPhysical coefficients modulations)) :=
    ContDiff.deriv' hsmooth
  have hsmoothSecond : ContDiff ℝ (2 : ℕ∞ω)
      (deriv (deriv (correctedPhysical coefficients modulations))) := ContDiff.deriv' hsmoothFirst
  have hsupport : Function.support (deriv (deriv (correctedPhysical coefficients modulations))) ⊆
      Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2) :=
    support_deriv_subset.trans (tsupport_deriv_subset.trans
      (correctedPhysical_tsupport_subset_four coefficients modulations))
  exact stripNorm_le_nodeUpper2348 sigma
    (deriv (deriv (correctedPhysical coefficients modulations)))
    hsmoothSecond (storedWidth 4 ^ 2) step zeroBound firstBound secondBound cells nodeUpper
    (sq_nonneg _) hstep hgrid hsupport hzero hfirst hsecond hnodes


end ConnesWeilRH.Dev
