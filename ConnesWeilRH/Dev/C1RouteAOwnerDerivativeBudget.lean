import ConnesWeilRH.Dev.C1RouteABumpDerivativeLadder
import ConnesWeilRH.Dev.C1RouteAWeightedChordPanel
import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def phaseCarrier2350 (modulation position : ℝ) : ℂ :=
  Complex.exp ((modulation * position : ℝ) * Complex.I)

noncomputable def familyDerivativeBudget2350 (order : ℕ) (coefficient : ℂ)
    (modulation radius : ℝ) : ℝ :=
  ‖coefficient‖ * ∑ index ∈ Finset.range (order + 1),
    (order.choose index : ℝ) * |modulation| ^ index *
      ((bumpConstant2350 (order - index) : ℝ) * Real.exp (-30) / radius ^ (order - index))

noncomputable def ownerDerivativeBudget2350 (order : ℕ)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) : ℝ :=
  ∑ index : Fin 30, familyDerivativeBudget2350 order (coefficients index)
    (modulations index) (storedWidth index ^ 2)

theorem phaseCarrier2350_hasDerivAt (modulation position : ℝ) :
    HasDerivAt (phaseCarrier2350 modulation)
      (((modulation : ℂ) * Complex.I) * phaseCarrier2350 modulation position) position := by
  have hphase := (((hasDerivAt_id position).const_mul modulation).ofReal_comp).mul_const Complex.I
  convert hphase.cexp using 1
  dsimp [phaseCarrier2350]
  simp only [mul_one]
  ring

theorem phaseCarrier2350_iteratedDeriv (order : ℕ) (modulation position : ℝ) :
    iteratedDeriv order (phaseCarrier2350 modulation) position =
      ((modulation : ℂ) * Complex.I) ^ order * phaseCarrier2350 modulation position := by
  induction order generalizing position with
  | zero => simp
  | succ order ih =>
    rw [iteratedDeriv_succ, funext ih]
    convert ((phaseCarrier2350_hasDerivAt modulation position).const_mul
      (((modulation : ℂ) * Complex.I) ^ order)).deriv using 1
    rw [pow_succ]
    ring

theorem phaseCarrier2350_iteratedDeriv_norm (order : ℕ) (modulation position : ℝ) :
    ‖iteratedDeriv order (phaseCarrier2350 modulation) position‖ = |modulation| ^ order := by
  rw [phaseCarrier2350_iteratedDeriv]
  simp [phaseCarrier2350, norm_pow, Complex.norm_exp]

theorem widthBump_ofReal_iteratedDeriv2350 (order : ℕ) {radius position : ℝ}
    (hradius : 0 < radius) :
    iteratedDeriv order (fun coordinate => (widthBump radius coordinate : ℂ)) position =
      (iteratedDeriv order (widthBump radius) position : ℝ) := by
  induction order generalizing position with
  | zero => rfl
  | succ order ih =>
    have hd := ContDiff.differentiable_iteratedDeriv' order
      ((widthBump_contDiff radius hradius).of_le
        (by exact_mod_cast (le_top : ((order + 1 : ℕ) : ℕ∞) ≤ ⊤)))
    rw [iteratedDeriv_succ, funext (fun coordinate => ih (position := coordinate)),
      (hd.differentiableAt.hasDerivAt.ofReal_comp).deriv,
      ← iteratedDeriv_succ]

theorem externalFamilyValue2344_iteratedDeriv_budget2350
    (order : ℕ) (horder : order ≤ 4) (coefficient : ℂ) (modulation : ℝ)
    {radius position : ℝ} (hradius : 0 < radius) :
    ‖iteratedDeriv order (externalFamilyValue2344 coefficient modulation radius) position‖ ≤
      familyDerivativeBudget2350 order coefficient modulation radius := by
  have hcarrierSmooth : ContDiff ℝ ∞ (phaseCarrier2350 modulation) := by
    have hphase : ContDiff ℝ ∞ (fun coordinate : ℝ =>
        (modulation * coordinate : ℝ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul contDiff_id)).mul contDiff_const
    exact Complex.contDiff_exp.comp hphase
  have hbumpSmooth : ContDiff ℝ ∞ (fun coordinate => (widthBump radius coordinate : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp (widthBump_contDiff radius hradius)
  have hcarrier : ContDiffAt ℝ order (phaseCarrier2350 modulation) position :=
    (hcarrierSmooth.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  have hbump : ContDiffAt ℝ order (fun coordinate => (widthBump radius coordinate : ℂ)) position :=
    (hbumpSmooth.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  have heq : externalFamilyValue2344 coefficient modulation radius =
      (fun coordinate => coefficient *
        (phaseCarrier2350 modulation coordinate * (widthBump radius coordinate : ℂ))) := by
    funext coordinate
    rw [externalFamilyValue2344_eq_familyTerm]
    dsimp [phaseCarrier2350]
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul hcarrier hbump, norm_mul]
  unfold familyDerivativeBudget2350
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg coefficient)
  calc
    _ ≤ ∑ index ∈ Finset.range (order + 1),
        ‖(order.choose index : ℂ) * iteratedDeriv index (phaseCarrier2350 modulation) position *
          iteratedDeriv (order - index)
            (fun coordinate => (widthBump radius coordinate : ℂ)) position‖ :=
      norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun index hindex => by
      rw [norm_mul, norm_mul, Complex.norm_natCast, phaseCarrier2350_iteratedDeriv_norm,
        widthBump_ofReal_iteratedDeriv2350 _ hradius, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (widthBump_iteratedDeriv_abs_le2350 (order - index)
          (le_trans (Nat.sub_le order index) horder) hradius)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg _) _))

theorem correctedPhysical_iteratedDeriv_budget2350 (order : ℕ) (horder : order ≤ 4)
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (position : ℝ) :
    ‖iteratedDeriv order (correctedPhysical coefficients modulations) position‖ ≤
      ownerDerivativeBudget2350 order coefficients modulations := by
  rw [← externalPhysical2344_eq_correctedPhysical]
  have hsmooth : ∀ index : Fin 30, ContDiffAt ℝ order
      (externalFamilyValue2344 (coefficients index) (modulations index) (storedWidth index ^ 2))
        position := fun index =>
    ((externalFamilyValue2344_contDiff _ _ _ (pow_pos (storedWidth_pos index) 2)).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  unfold externalPhysical2344
  rw [iteratedDeriv_fun_sum (fun index _ => hsmooth index)]
  unfold ownerDerivativeBudget2350
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun index _ =>
    externalFamilyValue2344_iteratedDeriv_budget2350 order horder _ _
      (pow_pos (storedWidth_pos index) 2))


theorem correctedPhysical_stripNorm_le_nodeUpper_from_budget2350
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma step : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ)
    (hstep : 0 < step) (hgrid : (cells : ℝ) * step = 2 * storedWidth 4 ^ 2)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
        ‖correctedPhysical coefficients modulations (-(storedWidth 4 ^ 2) + index * step)‖ ≤
          nodeUpper index) :
    stripNorm sigma (correctedPhysical coefficients modulations) ≤
      compositeNodeUpper2347 nodeUpper step cells + step ^ 2 * (2 * storedWidth 4 ^ 2) *
        weightedCurvature2348 sigma (storedWidth 4 ^ 2)
          (ownerDerivativeBudget2350 0 coefficients modulations)
          (ownerDerivativeBudget2350 1 coefficients modulations)
          (ownerDerivativeBudget2350 2 coefficients modulations) / 12 := by
  apply correctedPhysical_stripNorm_le_nodeUpper2348 coefficients modulations sigma step
    (ownerDerivativeBudget2350 0 coefficients modulations)
    (ownerDerivativeBudget2350 1 coefficients modulations)
    (ownerDerivativeBudget2350 2 coefficients modulations) cells nodeUpper hstep hgrid
  · intro position _
    simpa only [iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 0 (by decide) coefficients modulations position
  · intro position _
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 1 (by decide) coefficients modulations position
  · intro position _
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 2 (by decide) coefficients modulations position
  · exact hnodes

theorem correctedPhysical_stripSecondNorm_le_nodeUpper_from_budget2350
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (sigma step : ℝ) (cells : ℕ) (nodeUpper : ℕ → ℝ)
    (hstep : 0 < step) (hgrid : (cells : ℝ) * step = 2 * storedWidth 4 ^ 2)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-(storedWidth 4 ^ 2) + index * step)) *
        ‖deriv (deriv (correctedPhysical coefficients modulations))
          (-(storedWidth 4 ^ 2) + index * step)‖ ≤ nodeUpper index) :
    stripSecondNorm sigma (correctedPhysical coefficients modulations) ≤
      compositeNodeUpper2347 nodeUpper step cells + step ^ 2 * (2 * storedWidth 4 ^ 2) *
        weightedCurvature2348 sigma (storedWidth 4 ^ 2)
          (ownerDerivativeBudget2350 2 coefficients modulations)
          (ownerDerivativeBudget2350 3 coefficients modulations)
          (ownerDerivativeBudget2350 4 coefficients modulations) / 12 := by
  apply correctedPhysical_stripSecondNorm_le_nodeUpper2348 coefficients modulations sigma step
    (ownerDerivativeBudget2350 2 coefficients modulations)
    (ownerDerivativeBudget2350 3 coefficients modulations)
    (ownerDerivativeBudget2350 4 coefficients modulations) cells nodeUpper hstep hgrid
  · intro position _
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 2 (by decide) coefficients modulations position
  · intro position _
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 3 (by decide) coefficients modulations position
  · intro position _
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      correctedPhysical_iteratedDeriv_budget2350 4 (by decide) coefficients modulations position
  · exact hnodes

end ConnesWeilRH.Dev
