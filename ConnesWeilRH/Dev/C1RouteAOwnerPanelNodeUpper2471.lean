import ConnesWeilRH.Dev.C1RouteAOwnerStripAttachment2469

/-  2471: construct the nodeUpper input from the actual-owner local panel.

At each affine-grid node, use the half-step panel around that node.  The
rectangle and norm bounds are those of the exact 2460 owner; no numerical
value from the older 2275 node certificate is imported.  This removes the
external node-membership premise from the 2469 attachment.  Pricing the
resulting composite bound remains a separate certificate obligation.
-/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

noncomputable def ownerGridNode2471 (radius step : ℝ) (index : ℕ) : ℝ :=
  -radius + (index : ℝ) * step

noncomputable def ownerPanelNodeUpper2471
    (sigma radius step : ℝ) (index : ℕ) : ℝ :=
  Real.exp (sigma * ownerGridNode2471 radius step index) *
    ownerPanelNormBox_2467
      (ownerGridNode2471 radius step index - step / 2)
      (ownerGridNode2471 radius step index + step / 2)

theorem ownerPanelNodeUpper2471_bound
    (sigma radius step : ℝ) (index : ℕ) (hstep : 0 < step) :
    Real.exp (sigma * ownerGridNode2471 radius step index) *
        ‖ownerPanelSumValue_2467 (ownerGridNode2471 radius step index)‖ ≤
      ownerPanelNodeUpper2471 sigma radius step index := by
  unfold ownerPanelNodeUpper2471
  apply ownerPanelWeightedNormBound_2467
  · linarith
  · constructor <;> linarith

theorem ownerPanelStripNorm_le_panelNodeUpper_2471
    (sigma radius step zeroBound firstBound secondBound : ℝ) (cells : ℕ)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (cells : ℝ) * step = 2 * radius)
    (hzero : ownerPanelNormBox_2467 (-radius) radius ≤ zeroBound)
    (hfirst : ownerDerivativeBudget_2468 1 ≤ firstBound)
    (hsecond : ownerDerivativeBudget_2468 2 ≤ secondBound) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step cells +
        step ^ 2 * (2 * radius) *
          weightedCurvature2348 sigma radius zeroBound firstBound secondBound / 12 := by
  apply ownerPanelStripNorm_le_nodeUpper_2469 sigma radius step zeroBound
    firstBound secondBound cells (ownerPanelNodeUpper2471 sigma radius step)
    hradius hR hstep hgrid hzero hfirst hsecond
  intro index hindex
  exact ownerPanelNodeUpper2471_bound sigma radius step index hstep

end ConnesWeilRH.Dev
