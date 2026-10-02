import ConnesWeilRH.Dev.C1RouteAOwnerPanelNormBridge2467

/-  2470: first concrete node-upper read for the actual 2460 owner.

The older 2453/2454 node certificate belongs to the 2275 captured owner and
is deliberately not imported here.  This file instead closes one production
grid node, x = 1/4, using the universal 2466 owner panel and its norm bridge.
The remaining nodes must be generated and certified against this same owner.
-/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

noncomputable def ownerNodeUpper2470 (index : ℕ) : ℝ :=
  if index = 0 then ownerPanelNormBox_2467 X0_2460 X1_2460 else 0

theorem ownerNodeUpper2470_zero :
    ‖ownerPanelSumValue_2467 (1 / 4 : ℝ)‖ ≤ ownerNodeUpper2470 0 := by
  rw [ownerNodeUpper2470]
  simp only
  apply ownerPanelNormBound_2467
  · norm_num [X0_2460, X1_2460]
  · constructor <;> norm_num [X0_2460, X1_2460]

end ConnesWeilRH.Dev
