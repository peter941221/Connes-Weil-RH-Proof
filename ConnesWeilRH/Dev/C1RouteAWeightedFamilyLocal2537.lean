import ConnesWeilRH.Dev.C1RouteACoupledBumpEnvelope2536
import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget

/-!
Exact weighted external-family derivatives and the local order-0..4 bound.
The modulation stays signed in the complex derivative multiplier. The norm
bound applies to the existing owner function, including its support boundary.
-/

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def weightedPhase2537 (sigma modulation position : ℝ) : ℂ :=
  weightedExp2348 sigma position * phaseCarrier2350 modulation position

noncomputable def weightedLambda2537 (sigma modulation : ℝ) : ℂ :=
  (sigma : ℂ) + (modulation : ℂ) * Complex.I

theorem weightedPhase2537_hasDerivAt (sigma modulation position : ℝ) :
    HasDerivAt (weightedPhase2537 sigma modulation)
      (weightedLambda2537 sigma modulation * weightedPhase2537 sigma modulation position)
      position := by
  convert ((weightedExp2348_hasDerivAt sigma position).mul
    (phaseCarrier2350_hasDerivAt modulation position)) using 1
  dsimp [weightedPhase2537, weightedLambda2537]
  ring

theorem weightedPhase2537_contDiff (sigma modulation : ℝ) :
    ContDiff ℝ ∞ (weightedPhase2537 sigma modulation) := by
  have hweight : ContDiff ℝ ∞ (weightedExp2348 sigma) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hphase : ContDiff ℝ ∞ (phaseCarrier2350 modulation) := by
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
  exact hweight.mul hphase

theorem weightedPhase2537_iteratedDeriv (order : ℕ) (sigma modulation position : ℝ) :
    iteratedDeriv order (weightedPhase2537 sigma modulation) position =
      weightedLambda2537 sigma modulation ^ order *
        weightedPhase2537 sigma modulation position := by
  induction order generalizing position with
  | zero => simp
  | succ order ih =>
    rw [iteratedDeriv_succ, funext ih]
    convert ((weightedPhase2537_hasDerivAt sigma modulation position).const_mul
      (weightedLambda2537 sigma modulation ^ order)).deriv using 1
    rw [pow_succ]
    ring

theorem weightedPhase2537_iteratedDeriv_norm
    (order : ℕ) (sigma modulation position : ℝ) :
    ‖iteratedDeriv order (weightedPhase2537 sigma modulation) position‖ =
      ‖weightedLambda2537 sigma modulation‖ ^ order * Real.exp (sigma * position) := by
  rw [weightedPhase2537_iteratedDeriv, norm_mul, norm_pow]
  simp [weightedPhase2537, weightedExp2348, phaseCarrier2350, Complex.norm_exp]

theorem weightedExternalFamily_eq2537 (sigma : ℝ) (coefficient : ℂ)
    (modulation radius : ℝ) :
    weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius) =
      (fun position => coefficient * (weightedPhase2537 sigma modulation position *
        (widthBump radius position : ℂ))) := by
  funext position
  rw [weightedFunction2348, externalFamilyValue2344_eq_familyTerm]
  dsimp [weightedPhase2537, phaseCarrier2350]
  ring

theorem weightedExternalFamily_iteratedDeriv2537
    (order : ℕ) (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius position : ℝ} (hradius : 0 < radius) :
    iteratedDeriv order
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius))
        position =
      coefficient * ∑ index ∈ Finset.range (order + 1),
        (order.choose index : ℂ) *
          iteratedDeriv index (weightedPhase2537 sigma modulation) position *
          (iteratedDeriv (order - index) (widthBump radius) position : ℝ) := by
  have hcarrier : ContDiffAt ℝ order (weightedPhase2537 sigma modulation) position :=
    ((weightedPhase2537_contDiff sigma modulation).of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  have hbumpSmooth : ContDiff ℝ ∞ (fun x => (widthBump radius x : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp (widthBump_contDiff radius hradius)
  have hbump : ContDiffAt ℝ order (fun x => (widthBump radius x : ℂ)) position :=
    (hbumpSmooth.of_le (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).contDiffAt
  rw [weightedExternalFamily_eq2537, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul hcarrier hbump]
  simp only [widthBump_ofReal_iteratedDeriv2350 _ hradius]

noncomputable def weightedFamilyLocalUpper2537 (order : ℕ)
    (coefficient : ℂ) (sigma modulation radius near far position : ℝ) : ℝ :=
  ‖coefficient‖ * (Real.exp (sigma * position) *
    ∑ index ∈ Finset.range (order + 1),
      (order.choose index : ℝ) * ‖weightedLambda2537 sigma modulation‖ ^ index *
        localCoupledBumpUpper2536 (order - index) radius near far)

theorem weightedExternalFamily_iteratedDeriv_le_local2537
    (order : ℕ) (horder : order ≤ 4) (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius position near far : ℝ} (hradius : 0 < radius)
    (hnear : 0 ≤ near) (hnear_one : near < 1)
    (hlower : near ≤ |position / radius|) (hupper : |position / radius| ≤ far) :
    ‖iteratedDeriv order
      (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius))
      position‖ ≤ weightedFamilyLocalUpper2537 order coefficient
        sigma modulation radius near far position := by
  rw [weightedExternalFamily_iteratedDeriv2537 order sigma coefficient modulation hradius,
    norm_mul]
  unfold weightedFamilyLocalUpper2537
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg coefficient)
  calc
    _ ≤ ∑ index ∈ Finset.range (order + 1),
        ‖(order.choose index : ℂ) *
          iteratedDeriv index (weightedPhase2537 sigma modulation) position *
          (iteratedDeriv (order - index) (widthBump radius) position : ℝ)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro index _
      rw [norm_mul, norm_mul, Complex.norm_natCast, weightedPhase2537_iteratedDeriv_norm,
        Complex.norm_real, Real.norm_eq_abs]
      have hb := widthBump_iteratedDeriv_abs_le_local2536 (order - index)
        (le_trans (Nat.sub_le order index) horder) hradius hnear hnear_one hlower hupper
      calc
        _ ≤ (order.choose index : ℝ) *
            (‖weightedLambda2537 sigma modulation‖ ^ index * Real.exp (sigma * position)) *
            localCoupledBumpUpper2536 (order - index) radius near far :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ = _ := by ring

end ConnesWeilRH.Dev
