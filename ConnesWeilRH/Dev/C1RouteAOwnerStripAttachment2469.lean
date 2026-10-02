import ConnesWeilRH.Dev.C1RouteAOwnerDerivativeBudget2468
import ConnesWeilRH.Dev.C1RouteAOwnerSupport

/-  2469: assemble the actual-owner strip attachment.

This theorem consumes explicit owner budget and node-upper hypotheses and
instantiates the existing 2348 composite-node bound.  It is an attachment
interface, not a numerical certificate: nodeUpper and the three budget
comparisons remain visible premises. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators ContDiff

set_option linter.style.longLine false

theorem ownerPanelStripNorm_le_nodeUpper_2469
    (sigma radius step zeroBound firstBound secondBound : ℝ) (cells : ℕ)
    (nodeUpper : ℕ → ℝ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hzero : ownerPanelNormBox_2467 (-radius) radius ≤ zeroBound)
    (hfirst : ownerDerivativeBudget_2468 1 ≤ firstBound)
    (hsecond : ownerDerivativeBudget_2468 2 ≤ secondBound)
    (hnodes : ∀ index ≤ cells,
      Real.exp (sigma * (-radius + index * step)) *
        ‖ownerPanelSumValue_2467 (-radius + index * step)‖ ≤ nodeUpper index) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347 nodeUpper step cells + step ^ 2 * (2 * radius) *
        weightedCurvature2348 sigma radius zeroBound firstBound secondBound / 12 := by
  let family := fun i : Fin 30 =>
    externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
      (ownerRad_2463 i)
  have hfamily : ∀ i : Fin 30,
      ContDiff ℝ (2 : WithTop (WithTop ℕ)) (family i) := fun i =>
    (externalFamilyValue2344_contDiff _ _ _ (ownerRadPos_2465 i)).of_le
      (by decide)
  have hsmooth : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      ownerPanelSumValue_2467 := by
    rw [show ownerPanelSumValue_2467 = fun y => ∑ i : Fin 30, family i y by
      funext y; rfl]
    exact ContDiff.sum (s := Finset.univ) (fun i _ => hfamily i)
  have hsupport : Function.support ownerPanelSumValue_2467 ⊆
      Set.Icc (-radius) radius := by
    intro x hx
    by_contra hxr
    apply hx
    rw [show ownerPanelSumValue_2467 x =
        ∑ i : Fin 30, family i x by rfl]
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : ¬ |x| < ownerRad_2463 i := by
      intro hinside
      apply hxr
      exact Set.Icc_subset_Icc
        (neg_le_neg (hR i)) (hR i)
        ⟨le_of_lt (abs_lt.mp hinside).1, le_of_lt (abs_lt.mp hinside).2⟩
    simp [family, externalFamilyValue2344, hnot]
  apply stripNorm_le_nodeUpper2348 sigma ownerPanelSumValue_2467 hsmooth
    radius step zeroBound firstBound secondBound cells nodeUpper hradius hstep hgrid
    hsupport
  · intro position hposition
    exact (ownerPanelNormBound_2467
      (by linarith [hposition.1, hposition.2]) hposition).trans hzero
  · intro position hposition
    have h := ownerPanelIteratedDerivBudget_2468 1 (by decide) position
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h.trans hfirst
  · intro position hposition
    have h := ownerPanelSecondDerivBudget_2468 position
    exact h.trans hsecond
  · exact hnodes

end ConnesWeilRH.Dev
