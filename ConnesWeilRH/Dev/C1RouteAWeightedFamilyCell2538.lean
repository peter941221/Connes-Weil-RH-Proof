import ConnesWeilRH.Dev.C1RouteAWeightedFamilyLocal2537
import ConnesWeilRH.Dev.C1RouteAWholeCellLipschitz2534
import Mathlib.Analysis.Calculus.MeanValue

/-!
Whole-cell third-derivative bounds for the existing weighted external family.
The fourth-derivative majorant is derived from radius geometry and the proved
local bump envelope, rather than supplied as an analytic premise.
-/

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def weightedFamilyCellUpper2538 (order : ℕ) (coefficient : ℂ)
    (sigma modulation radius near far a b : ℝ) : ℝ :=
  ‖coefficient‖ * (Real.exp (max (sigma * a) (sigma * b)) *
    ∑ index ∈ Finset.range (order + 1),
      (order.choose index : ℝ) * ‖weightedLambda2537 sigma modulation‖ ^ index *
        localCoupledBumpUpper2536 (order - index) radius near far)

theorem localCoupledBumpUpper2536_nonneg (order : ℕ) {radius near far : ℝ}
    (hradius : 0 < radius) (hnear : 0 ≤ near) (hnear_one : near < 1)
    (hfar : 0 ≤ far) : 0 ≤ localCoupledBumpUpper2536 order radius near far := by
  have hp := bumpNumeratorAbsUpper2536_nonneg order hfar
  have hq : 0 < 1 - near ^ 2 := by nlinarith
  unfold localCoupledBumpUpper2536
  positivity

theorem weightedExternalFamily_iteratedDeriv_le_cell2538
    (order : ℕ) (horder : order ≤ 4) (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius near far a b position : ℝ} (hradius : 0 < radius)
    (hnear : 0 ≤ near) (hnear_one : near < 1)
    (hlower : near ≤ |position / radius|) (hupper : |position / radius| ≤ far)
    (hposition : position ∈ Set.Icc a b) :
    ‖iteratedDeriv order
      (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius))
      position‖ ≤ weightedFamilyCellUpper2538 order coefficient
        sigma modulation radius near far a b := by
  have hweight : sigma * position ≤ max (sigma * a) (sigma * b) := by
    rcases le_total 0 sigma with hs | hs
    · exact (mul_le_mul_of_nonneg_left hposition.2 hs).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hposition.1 hs).trans (le_max_left _ _)
  have hsum : 0 ≤ ∑ index ∈ Finset.range (order + 1),
      (order.choose index : ℝ) * ‖weightedLambda2537 sigma modulation‖ ^ index *
        localCoupledBumpUpper2536 (order - index) radius near far := by
    apply Finset.sum_nonneg
    intro index _
    exact mul_nonneg (by positivity)
      (localCoupledBumpUpper2536_nonneg _ hradius hnear hnear_one
        ((abs_nonneg _).trans hupper))
  apply (weightedExternalFamily_iteratedDeriv_le_local2537 order horder sigma coefficient
    modulation hradius hnear hnear_one hlower hupper).trans
  unfold weightedFamilyLocalUpper2537 weightedFamilyCellUpper2538
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hweight) hsum) (norm_nonneg _)

theorem weightedExternalFamily_contDiff2538 (sigma : ℝ) (coefficient : ℂ)
    (modulation : ℝ) {radius : ℝ} (hradius : 0 < radius) :
    ContDiff ℝ ∞
      (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) := by
  rw [weightedExternalFamily_eq2537]
  have hbump : ContDiff ℝ ∞ (fun x => (widthBump radius x : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp (widthBump_contDiff radius hradius)
  exact contDiff_const.mul ((weightedPhase2537_contDiff sigma modulation).mul hbump)

theorem weightedExternalFamily_iteratedDeriv_zero_outside2538
    (order : ℕ) (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius position : ℝ} (hradius : 0 < radius) (houtside : radius ≤ |position|) :
    iteratedDeriv order
      (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius))
      position = 0 := by
  rw [weightedExternalFamily_iteratedDeriv2537 order sigma coefficient modulation hradius]
  simp only [widthBump_iteratedDeriv_outside2350 _ hradius houtside,
    Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]

theorem weightedExternalFamily_third_le_endpoints2538
    (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius near far a b : ℝ} (hradius : 0 < radius) (hab : a ≤ b)
    (hnear : 0 ≤ near) (hnear_one : near < 1) (hfar : 0 ≤ far)
    (hgeometry : ∀ x ∈ Set.Icc a b, |x| < radius →
      near ≤ |x / radius| ∧ |x / radius| ≤ far) :
    ∀ x ∈ Set.Icc a b,
      ‖iteratedDeriv 3
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) x‖ ≤
      max
        ‖iteratedDeriv 3
          (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) a‖
        ‖iteratedDeriv 3
          (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) b‖ +
      weightedFamilyCellUpper2538 4 coefficient sigma modulation radius near far a b *
        ((b - a) / 2) := by
  let f := weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)
  let L := weightedFamilyCellUpper2538 4 coefficient sigma modulation radius near far a b
  have hfourth : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv 4 f x‖ ≤ L := by
    intro x hx
    by_cases hinside : |x| < radius
    · exact weightedExternalFamily_iteratedDeriv_le_cell2538 4 (by decide) sigma coefficient
        modulation hradius hnear hnear_one
        (hgeometry x hx hinside).1 (hgeometry x hx hinside).2 hx
    · have hz := weightedExternalFamily_iteratedDeriv_zero_outside2538 4 sigma coefficient
        modulation hradius (not_lt.mp hinside)
      change ‖iteratedDeriv 4
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) x‖ ≤ L
      rw [hz, norm_zero]
      have hsum : 0 ≤ ∑ index ∈ Finset.range (4 + 1),
          (Nat.choose 4 index : ℝ) * ‖weightedLambda2537 sigma modulation‖ ^ index *
            localCoupledBumpUpper2536 (4 - index) radius near far := by
        apply Finset.sum_nonneg
        intro index _
        exact mul_nonneg (by positivity)
          (localCoupledBumpUpper2536_nonneg _ hradius hnear hnear_one hfar)
      dsimp [L, weightedFamilyCellUpper2538]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) hsum)
  have hL : 0 ≤ L := (norm_nonneg _).trans (hfourth a ⟨le_rfl, hab⟩)
  have hsmooth : ContDiff ℝ ∞ f :=
    weightedExternalFamily_contDiff2538 sigma coefficient modulation hradius
  have hd : Differentiable ℝ (iteratedDeriv 3 f) :=
    ContDiff.differentiable_iteratedDeriv' 3 (hsmooth.of_le (by decide))
  have hLip : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      ‖iteratedDeriv 3 f x - iteratedDeriv 3 f y‖ ≤ L * |x-y| := by
    intro x y hx hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hd x)
      (fun x hx => by simpa only [← iteratedDeriv_succ] using hfourth x hx)
      (convex_Icc a b) hy hx
    simpa only [Real.norm_eq_abs] using h
  exact fun x hx => norm_le_endpoint_max_add_half_lipschitz2534
    (iteratedDeriv 3 f) a b L hab hL hLip hx

noncomputable def cellNearAbs2538 (a b : ℝ) : ℝ :=
  if a ≤ 0 ∧ 0 ≤ b then 0 else min |a| |b|

theorem cellNearAbs2538_nonneg (a b : ℝ) : 0 ≤ cellNearAbs2538 a b := by
  unfold cellNearAbs2538
  split_ifs
  · exact le_rfl
  · exact le_min (abs_nonneg _) (abs_nonneg _)

theorem cellNearAbs2538_le {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    cellNearAbs2538 a b ≤ |x| := by
  unfold cellNearAbs2538
  split_ifs with hcross
  · exact abs_nonneg _
  · by_cases ha : a ≤ 0
    · have hb : b < 0 := lt_of_not_ge (fun hb => hcross ⟨ha, hb⟩)
      have hxneg : x ≤ 0 := hx.2.trans hb.le
      apply (min_le_right |a| |b|).trans
      rw [abs_of_neg hb, abs_of_nonpos hxneg]
      exact neg_le_neg hx.2
    · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
      apply (min_le_left |a| |b|).trans
      rw [abs_of_nonneg ha0, abs_of_nonneg (ha0.trans hx.1)]
      exact hx.1

theorem cellAbs_le_max2538 {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    |x| ≤ max |a| |b| := by
  apply abs_le.mpr
  constructor
  · have ha := neg_le_abs a
    have hm := le_max_left |a| |b|
    linarith [hx.1]
  · exact hx.2.trans ((le_abs_self b).trans (le_max_right _ _))

noncomputable def weightedFamilyThirdCellUpper2538
    (sigma : ℝ) (coefficient : ℂ) (modulation radius a b : ℝ) : ℝ :=
  if cellNearAbs2538 a b < radius then
    max
      ‖iteratedDeriv 3
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) a‖
      ‖iteratedDeriv 3
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) b‖ +
    weightedFamilyCellUpper2538 4 coefficient sigma modulation radius
      (cellNearAbs2538 a b / radius) (min (max |a| |b|) radius / radius) a b * ((b-a)/2)
  else 0

theorem weightedExternalFamily_third_le_cell2538
    (sigma : ℝ) (coefficient : ℂ) (modulation : ℝ)
    {radius a b : ℝ} (hradius : 0 < radius) (hab : a ≤ b) :
    ∀ x ∈ Set.Icc a b,
      ‖iteratedDeriv 3
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) x‖ ≤
      weightedFamilyThirdCellUpper2538 sigma coefficient modulation radius a b := by
  intro x hx
  unfold weightedFamilyThirdCellUpper2538
  split_ifs with hintersects
  · apply weightedExternalFamily_third_le_endpoints2538 sigma coefficient modulation
      hradius hab
      (div_nonneg (cellNearAbs2538_nonneg a b) hradius.le)
      ((div_lt_one hradius).mpr hintersects)
      (div_nonneg (le_min (le_max_of_le_left (abs_nonneg a)) hradius.le) hradius.le)
      _ x hx
    intro y hy hyinside
    rw [abs_div, abs_of_pos hradius]
    exact ⟨div_le_div_of_nonneg_right (cellNearAbs2538_le hy) hradius.le,
      div_le_div_of_nonneg_right (le_min (cellAbs_le_max2538 hy) hyinside.le) hradius.le⟩
  · have houtside : radius ≤ |x| :=
      (not_lt.mp hintersects).trans (cellNearAbs2538_le hx)
    rw [weightedExternalFamily_iteratedDeriv_zero_outside2538 3 sigma coefficient
      modulation hradius houtside, norm_zero]

theorem weightedFamilyCellUpper_four2538
    (coefficient : ℂ) (sigma modulation radius near far a b : ℝ) :
    weightedFamilyCellUpper2538 4 coefficient sigma modulation radius near far a b =
      ‖coefficient‖ * (Real.exp (max (sigma * a) (sigma * b)) *
        (localCoupledBumpUpper2536 4 radius near far +
          4 * ‖weightedLambda2537 sigma modulation‖ *
            localCoupledBumpUpper2536 3 radius near far +
          6 * ‖weightedLambda2537 sigma modulation‖ ^ 2 *
            localCoupledBumpUpper2536 2 radius near far +
          4 * ‖weightedLambda2537 sigma modulation‖ ^ 3 *
            localCoupledBumpUpper2536 1 radius near far +
          ‖weightedLambda2537 sigma modulation‖ ^ 4 *
            localCoupledBumpUpper2536 0 radius near far)) := by
  norm_num [weightedFamilyCellUpper2538, Finset.sum_range_succ, Nat.choose]

theorem weightedExternalFamily_third_le_coefficient_ball2538
    (sigma : ℝ) (coefficient center : ℂ) (error modulation : ℝ)
    {radius a b : ℝ} (hradius : 0 < radius) (hab : a ≤ b)
    (herror : ‖coefficient - center‖ ≤ error) :
    ∀ x ∈ Set.Icc a b,
      ‖iteratedDeriv 3
        (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) x‖ ≤
      (‖center‖ + error) * weightedFamilyThirdCellUpper2538 sigma 1 modulation radius a b := by
  intro x hx
  have hunit := weightedExternalFamily_third_le_cell2538 sigma 1 modulation hradius hab x hx
  have hbound_nonneg := (norm_nonneg _).trans hunit
  have hcoef : ‖coefficient‖ ≤ ‖center‖ + error := by
    calc
      ‖coefficient‖ = ‖center + (coefficient - center)‖ := by congr 1; ring
      _ ≤ ‖center‖ + ‖coefficient - center‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have heq : iteratedDeriv 3
      (weightedFunction2348 sigma (externalFamilyValue2344 coefficient modulation radius)) x =
      coefficient * iteratedDeriv 3
        (weightedFunction2348 sigma (externalFamilyValue2344 1 modulation radius)) x := by
    rw [weightedExternalFamily_iteratedDeriv2537 3 sigma coefficient modulation hradius,
      weightedExternalFamily_iteratedDeriv2537 3 sigma 1 modulation hradius]
    simp only [one_mul]
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_left hunit (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hcoef hbound_nonneg)

end ConnesWeilRH.Dev
