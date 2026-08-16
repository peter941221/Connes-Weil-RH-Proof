import ConnesWeilRH.Dev.C1XiCenterTwoHorizontalDecay
import ConnesWeilRH.Dev.C1XiContourDecay

/-!
# C1XiCenterTwoHorizontalBoundary - wide horizontal contour limit

This module applies the explicit center-`2` logarithmic-derivative envelope
to the two horizontal sides of the fixed wide rectangle with real interval
`[-1,2]`.  The interval length is `3`, so the two sides contribute the factor
`6` in the norm bound.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoHorizontalBoundary

open Set
open Filter
open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open C1XiVerticalFunctional
open C1XiContourDecay
open C1XiCenterTwoHorizontal
open C1XiCenterTwoHorizontalDecay
open scoped Interval Topology

noncomputable section

/-- The two oriented horizontal sides of the fixed wide rectangle. -/
noncomputable def wideHorizontalBoundaryIntegral
    (F : CompactLogTest) (T : Real) : Complex :=
  (∫ x : Real in (-1 : Real)..2,
      xiContourKernel F (verticalPoint x (-T))) -
    ∫ x : Real in (-1 : Real)..2,
      xiContourKernel F (verticalPoint x T)

/-- A fourth-order centered-weight estimate and a pointwise xi logarithmic-
derivative estimate bound one point of either horizontal side. -/
private theorem norm_xiContourKernel_wideHorizontal_le
    (F : CompactLogTest) {T M C sigma t : Real}
    (hT : 0 < T) (hM : 0 ≤ M)
    (hweight : ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ ≤ C)
    (hlog : ‖negativeXiLogDeriv (verticalPoint sigma t)‖ ≤ M)
    (ht : t = T ∨ t = -T) :
    ‖xiContourKernel F (verticalPoint sigma t)‖ ≤
      M * C / ‖T / (2 * Real.pi)‖ ^ 4 := by
  let q : Real := ‖T / (2 * Real.pi)‖ ^ 4
  have hdenom : 2 * Real.pi ≠ 0 := by positivity
  have hquot : T / (2 * Real.pi) ≠ 0 :=
    div_ne_zero hT.ne' hdenom
  have hqPos : 0 < q := pow_pos (norm_pos_iff.mpr hquot) 4
  have htq : ‖t / (2 * Real.pi)‖ ^ 4 = q := by
    rcases ht with rfl | rfl
    · rfl
    · simp [q]
  change ‖negativeXiLogDeriv (verticalPoint sigma t) *
      centeredLaplaceWeight F (verticalPoint sigma t)‖ ≤ M * C / q
  rw [norm_mul]
  apply (le_div_iff₀ hqPos).mpr
  calc
    ‖negativeXiLogDeriv (verticalPoint sigma t)‖ *
          ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ * q =
        ‖negativeXiLogDeriv (verticalPoint sigma t)‖ *
          (q * ‖centeredLaplaceWeight F (verticalPoint sigma t)‖) := by ring
    _ ≤ M * C := by
      apply mul_le_mul hlog
      · simpa only [htq] using hweight
      · exact mul_nonneg hqPos.le (norm_nonneg _)
      · exact hM

/-- The two wide horizontal sides are bounded by six times the pointwise
product budget. -/
theorem DyadicCenterTwoHorizontalData.norm_wideHorizontalBoundaryIntegral_le
    {n : Nat} (H : DyadicCenterTwoHorizontalData n)
    (F : CompactLogTest) {C : Real}
    (hweight : ∀ sigma ∈ Icc (-1 : Real) 2, ∀ t : Real,
      ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ ≤ C) :
    ‖wideHorizontalBoundaryIntegral F H.height‖ ≤
      6 * (dyadicCenterTwoXiLogDerivBound n * C /
        ‖H.height / (2 * Real.pi)‖ ^ 4) := by
  let P : Real := dyadicCenterTwoXiLogDerivBound n * C /
    ‖H.height / (2 * Real.pi)‖ ^ 4
  have hM : 0 ≤ dyadicCenterTwoXiLogDerivBound n :=
    dyadicCenterTwoXiLogDerivBound_nonneg n
  have hlowerPoint : ∀ x ∈ Icc (-1 : Real) 2,
      ‖xiContourKernel F (verticalPoint x (-H.height))‖ ≤ P := by
    intro x hx
    exact norm_xiContourKernel_wideHorizontal_le F H.height_pos hM
      (hweight x hx (-H.height)) (H.norm_negativeXiLogDeriv_lower_le hx)
      (Or.inr rfl)
  have hupperPoint : ∀ x ∈ Icc (-1 : Real) 2,
      ‖xiContourKernel F (verticalPoint x H.height)‖ ≤ P := by
    intro x hx
    exact norm_xiContourKernel_wideHorizontal_le F H.height_pos hM
      (hweight x hx H.height) (H.norm_negativeXiLogDeriv_upper_le hx)
      (Or.inl rfl)
  have hlowerIntegral :
      ‖∫ x : Real in (-1 : Real)..2,
          xiContourKernel F (verticalPoint x (-H.height))‖ ≤ 3 * P := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : Real)) (b := 2) (C := P)
      (f := fun x : Real => xiContourKernel F (verticalPoint x (-H.height)))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (-1 : Real) ≤ 2)] at hx
        exact hlowerPoint x ⟨le_of_lt hx.1, hx.2⟩)
    norm_num at hraw
    simpa only [mul_comm] using hraw
  have hupperIntegral :
      ‖∫ x : Real in (-1 : Real)..2,
          xiContourKernel F (verticalPoint x H.height)‖ ≤ 3 * P := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : Real)) (b := 2) (C := P)
      (f := fun x : Real => xiContourKernel F (verticalPoint x H.height))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (-1 : Real) ≤ 2)] at hx
        exact hupperPoint x ⟨le_of_lt hx.1, hx.2⟩)
    norm_num at hraw
    simpa only [mul_comm] using hraw
  unfold wideHorizontalBoundaryIntegral
  calc
    ‖(∫ x : Real in (-1 : Real)..2,
          xiContourKernel F (verticalPoint x (-H.height))) -
        ∫ x : Real in (-1 : Real)..2,
          xiContourKernel F (verticalPoint x H.height)‖ ≤
        ‖∫ x : Real in (-1 : Real)..2,
          xiContourKernel F (verticalPoint x (-H.height))‖ +
        ‖∫ x : Real in (-1 : Real)..2,
          xiContourKernel F (verticalPoint x H.height)‖ := norm_sub_le _ _
    _ ≤ 3 * P + 3 * P := add_le_add hlowerIntegral hupperIntegral
    _ = 6 * (dyadicCenterTwoXiLogDerivBound n * C /
          ‖H.height / (2 * Real.pi)‖ ^ 4) := by
      dsimp only [P]
      ring

/-- The scalar bound for the selected horizontal sequence tends to zero. -/
theorem tendsto_selected_wideHorizontal_scalar_bound
    {C : Real} :
    Tendsto
      (fun n : Nat =>
        6 * (dyadicCenterTwoXiLogDerivBound n * C /
          ‖selectedDyadicCenterTwoHeight n / (2 * Real.pi)‖ ^ 4))
      atTop (nhds 0) := by
  let K : Real := 6 * C * (2 * Real.pi) ^ 4
  have hbase := tendsto_dyadicCenterTwoXiLogDerivBound_div_height_pow_four
  have hscaled := hbase.const_mul K
  convert hscaled using 1
  · funext n
    let H := selectedDyadicCenterTwoHorizontalData n
    have hT : selectedDyadicCenterTwoHeight n = H.height := rfl
    have hTPos : 0 < selectedDyadicCenterTwoHeight n := by
      rw [hT]
      exact H.height_pos
    have hpiPos : 0 < 2 * Real.pi := by positivity
    have hnorm : ‖selectedDyadicCenterTwoHeight n / (2 * Real.pi)‖ =
        selectedDyadicCenterTwoHeight n / (2 * Real.pi) := by
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hTPos hpiPos)]
    rw [hnorm, div_pow]
    dsimp only [K]
    field_simp [hTPos.ne', Real.pi_ne_zero]
  · simp

/-- The actual two horizontal sides of the selected wide rectangles vanish. -/
theorem wideHorizontalBoundaryIntegral_tendsto_zero
    (F : CompactLogTest) :
    Tendsto
      (fun n : Nat => wideHorizontalBoundaryIntegral F
        (selectedDyadicCenterTwoHeight n))
      atTop (nhds 0) := by
  obtain ⟨C, _, hweight⟩ :=
    exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_wideStrip F
  apply squeeze_zero_norm
  · intro n
    exact DyadicCenterTwoHorizontalData.norm_wideHorizontalBoundaryIntegral_le
      (selectedDyadicCenterTwoHorizontalData n) F hweight
  · exact tendsto_selected_wideHorizontal_scalar_bound

end
end C1XiCenterTwoHorizontalBoundary
end Source
end ConnesWeilRH
