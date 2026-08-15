import ConnesWeilRH.Dev.C1XiContourDecay
import ConnesWeilRH.Dev.C1XiFiniteHeightRectangleAssembly

/-!
# C1XiHorizontalDecay - conditional horizontal xi-contour decay

The compact-log weight already has uniform fourth-order decay on the closed
critical strip. This module exposes the exact remaining input for a
horizontal-edge limit: a uniform bound for the negative xi logarithmic
derivative along the two selected horizontal segments.

The local finite-height factorization owner does not supply that envelope.
Accordingly, this file proves only the conditional product estimate and makes
no contour-limit, explicit-formula, or RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiHorizontalDecay

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20ZetaCounting
open C1XiContourDecay
open C1XiFiniteHeightRectangle
open C1XiFiniteHeightRectangleAssembly
open C1XiResidue
open C1XiVerticalFunctional
open scoped Interval

/-- A common bound for the negative xi logarithmic derivative on both
horizontal sides of the critical-strip rectangle at height `T`. This is the
genuinely analytic input left open by the finite-height factorization. -/
def xiHorizontalLogDerivEnvelope (T M : Real) : Prop :=
  0 <= M ∧
    ∀ sigma ∈ Set.Icc (0 : Real) 1,
      ‖negativeXiLogDeriv (verticalPoint sigma (-T))‖ <= M ∧
        ‖negativeXiLogDeriv (verticalPoint sigma T)‖ <= M

/-- A xi-zero-free horizontal boundary has a finite logarithmic-derivative
envelope at that one height. Compactness proves existence only; it supplies no
growth control as the height varies. -/
theorem exists_xiHorizontalLogDerivEnvelope
    (T : Real) (hheight : xiHeightBoundaryAvoidsZeros T) :
    ∃ M : Real, xiHorizontalLogDerivEnvelope T M := by
  have hlower_nonzero : ∀ x ∈ Set.Icc (0 : Real) 1,
      completedRiemannXi (verticalPoint x (-T)) ≠ 0 := by
    intro x hx
    simpa [verticalPoint] using hheight.1 x hx
  have hupper_nonzero : ∀ x ∈ Set.Icc (0 : Real) 1,
      completedRiemannXi (verticalPoint x T) ≠ 0 := by
    intro x hx
    simpa [verticalPoint] using hheight.2 x hx
  have hlower_map : Continuous (fun x : Real => verticalPoint x (-T)) := by
    unfold verticalPoint
    fun_prop
  have hupper_map : Continuous (fun x : Real => verticalPoint x T) := by
    unfold verticalPoint
    fun_prop
  have hlower_continuous : ContinuousOn
      (fun x : Real => ‖negativeXiLogDeriv (verticalPoint x (-T))‖)
      (Set.Icc (0 : Real) 1) := by
    intro x hx
    have hcontinuous : ContinuousAt
        (fun y : Real => negativeXiLogDeriv (verticalPoint y (-T))) x :=
      (differentiableAt_negativeXiLogDeriv_of_completedRiemannXi_ne_zero
        (hlower_nonzero x hx)).continuousAt.comp'
          (f := fun y : Real => verticalPoint y (-T)) (x := x)
          hlower_map.continuousAt
    exact hcontinuous.norm.continuousWithinAt
  have hupper_continuous : ContinuousOn
      (fun x : Real => ‖negativeXiLogDeriv (verticalPoint x T)‖)
      (Set.Icc (0 : Real) 1) := by
    intro x hx
    have hcontinuous : ContinuousAt
        (fun y : Real => negativeXiLogDeriv (verticalPoint y T)) x :=
      (differentiableAt_negativeXiLogDeriv_of_completedRiemannXi_ne_zero
        (hupper_nonzero x hx)).continuousAt.comp'
          (f := fun y : Real => verticalPoint y T) (x := x)
          hupper_map.continuousAt
    exact hcontinuous.norm.continuousWithinAt
  obtain ⟨Mlower, hMlower⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : Real) 1)).bddAbove_image
      hlower_continuous
  obtain ⟨Mupper, hMupper⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : Real) 1)).bddAbove_image
      hupper_continuous
  refine ⟨max 0 (max Mlower Mupper), le_max_left _ _, ?_⟩
  intro x hx
  constructor
  · exact (hMlower ⟨x, hx, rfl⟩).trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact (hMupper ⟨x, hx, rfl⟩).trans
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- A fourth-order centered-weight estimate times a horizontal logarithmic-
derivative envelope bounds one horizontal xi-contour kernel point. -/
private theorem norm_xiContourKernel_horizontal_le_of_logDerivEnvelope
    (F : CompactLogTest) {T M C sigma t : Real}
    (hT : 0 < T) (hM : 0 <= M)
    (hweight : ‖t / (2 * Real.pi)‖ ^ 4 *
        ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ <= C)
    (hlog : ‖negativeXiLogDeriv (verticalPoint sigma t)‖ <= M)
    (ht : t = T ∨ t = -T) :
    ‖xiContourKernel F (verticalPoint sigma t)‖ <=
      M * C / ‖T / (2 * Real.pi)‖ ^ 4 := by
  let q : Real := ‖T / (2 * Real.pi)‖ ^ 4
  have hdenom_ne : 2 * Real.pi ≠ 0 := by positivity
  have hquot_ne : T / (2 * Real.pi) ≠ 0 :=
    div_ne_zero (ne_of_gt hT) hdenom_ne
  have hq_pos : 0 < q := by
    exact pow_pos (norm_pos_iff.mpr hquot_ne) _
  have hq_nonneg : 0 <= q := hq_pos.le
  have htq : ‖t / (2 * Real.pi)‖ ^ 4 = q := by
    rcases ht with rfl | rfl
    · rfl
    · simp [q]
  change ‖negativeXiLogDeriv (verticalPoint sigma t) *
      centeredLaplaceWeight F (verticalPoint sigma t)‖ <= M * C / q
  rw [norm_mul]
  apply (le_div_iff₀ hq_pos).mpr
  calc
    ‖negativeXiLogDeriv (verticalPoint sigma t)‖ *
        ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ * q =
      ‖negativeXiLogDeriv (verticalPoint sigma t)‖ *
        (q * ‖centeredLaplaceWeight F (verticalPoint sigma t)‖) := by ring
    _ <= M * C := by
      apply mul_le_mul hlog
      · simpa only [htq] using hweight
      · exact mul_nonneg hq_nonneg (norm_nonneg _)
      · exact hM

/-- Given a selected-height envelope for `xi'/xi`, the two horizontal sides of
the finite critical-strip contour are bounded by that envelope times the
uniform fourth-order test-weight decay. -/
theorem exists_quartic_horizontalBoundary_bound_of_logDerivEnvelope
    (F : CompactLogTest) (T M : Real) (hT : 0 < T)
    (henvelope : xiHorizontalLogDerivEnvelope T M) :
    ∃ C : Real, 0 <= C ∧
      ‖criticalStripHorizontalBoundaryIntegral F T‖ <=
        2 * (M * C / ‖T / (2 * Real.pi)‖ ^ 4) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_criticalStrip F
  rcases henvelope with ⟨hM, henvelope⟩
  refine ⟨C, hC, ?_⟩
  have hlower_point : ∀ x ∈ Set.Icc (0 : Real) 1,
      ‖xiContourKernel F (verticalPoint x (-T))‖ <=
        M * C / ‖T / (2 * Real.pi)‖ ^ 4 := by
    intro x hx
    exact norm_xiContourKernel_horizontal_le_of_logDerivEnvelope F hT hM
      (hweight x hx (-T)) (henvelope x hx).1 (Or.inr rfl)
  have hupper_point : ∀ x ∈ Set.Icc (0 : Real) 1,
      ‖xiContourKernel F (verticalPoint x T)‖ <=
        M * C / ‖T / (2 * Real.pi)‖ ^ 4 := by
    intro x hx
    exact norm_xiContourKernel_horizontal_le_of_logDerivEnvelope F hT hM
      (hweight x hx T) (henvelope x hx).2 (Or.inl rfl)
  have hlower_integral :
      ‖∫ x : Real in (0 : Real)..1,
          xiContourKernel F (verticalPoint x (-T))‖ <=
        M * C / ‖T / (2 * Real.pi)‖ ^ 4 := by
    simpa using (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : Real)) (b := 1)
      (C := M * C / ‖T / (2 * Real.pi)‖ ^ 4)
      (f := fun x : Real => xiContourKernel F (verticalPoint x (-T)))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (0 : Real) <= 1)] at hx
        exact hlower_point x ⟨le_of_lt hx.1, hx.2⟩))
  have hupper_integral :
      ‖∫ x : Real in (0 : Real)..1,
          xiContourKernel F (verticalPoint x T)‖ <=
        M * C / ‖T / (2 * Real.pi)‖ ^ 4 := by
    simpa using (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : Real)) (b := 1)
      (C := M * C / ‖T / (2 * Real.pi)‖ ^ 4)
      (f := fun x : Real => xiContourKernel F (verticalPoint x T))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (0 : Real) <= 1)] at hx
        exact hupper_point x ⟨le_of_lt hx.1, hx.2⟩))
  unfold criticalStripHorizontalBoundaryIntegral
  rw [criticalStripRectangleLower_re, criticalStripRectangleUpper_re,
    criticalStripRectangleLower_im, criticalStripRectangleUpper_im]
  simpa only [verticalPoint] using
    (calc
      ‖(∫ x : Real in (0 : Real)..1,
          xiContourKernel F (verticalPoint x (-T))) -
          ∫ x : Real in (0 : Real)..1,
            xiContourKernel F (verticalPoint x T)‖ <=
          ‖∫ x : Real in (0 : Real)..1,
            xiContourKernel F (verticalPoint x (-T))‖ +
            ‖∫ x : Real in (0 : Real)..1,
              xiContourKernel F (verticalPoint x T)‖ := norm_sub_le _ _
      _ <= (M * C / ‖T / (2 * Real.pi)‖ ^ 4) +
          (M * C / ‖T / (2 * Real.pi)‖ ^ 4) :=
        add_le_add hlower_integral hupper_integral
      _ = 2 * (M * C / ‖T / (2 * Real.pi)‖ ^ 4) := by ring)

/-- A positive xi-zero-free critical-strip height has a finite horizontal
contour bound. This is pointwise in the chosen height and has no asymptotic
decay claim. -/
theorem exists_quartic_horizontalBoundary_bound_of_xiHeightBoundaryAvoidsZeros
    (F : CompactLogTest) (T : Real) (hT : 0 < T)
    (hheight : xiHeightBoundaryAvoidsZeros T) :
    ∃ M C : Real, 0 <= M ∧ 0 <= C ∧
      ‖criticalStripHorizontalBoundaryIntegral F T‖ <=
        2 * (M * C / ‖T / (2 * Real.pi)‖ ^ 4) := by
  obtain ⟨M, hM⟩ := exists_xiHorizontalLogDerivEnvelope T hheight
  obtain ⟨C, hC, hbound⟩ :=
    exists_quartic_horizontalBoundary_bound_of_logDerivEnvelope F T M hT hM
  exact ⟨M, C, hM.1, hC, hbound⟩

/-- The finite-height rectangle owner supplies the local hypotheses for a
finite horizontal bound, but does not make its bound uniform across owners. -/
theorem XiHeightRectangleFactorData.exists_quartic_horizontalBoundary_bound
    (D : XiHeightRectangleFactorData) (F : CompactLogTest) :
    ∃ M C : Real, 0 <= M ∧ 0 <= C ∧
      ‖criticalStripHorizontalBoundaryIntegral F D.height‖ <=
        2 * (M * C / ‖D.height / (2 * Real.pi)‖ ^ 4) := by
  exact exists_quartic_horizontalBoundary_bound_of_xiHeightBoundaryAvoidsZeros
    F D.height D.height_pos D.boundary_avoids

end C1XiHorizontalDecay
end Source
end ConnesWeilRH
