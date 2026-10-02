import ConnesWeilRH.Dev.C1RouteAOwnerCurvatureTable2481
import ConnesWeilRH.Dev.C1RouteAOwnerLocalCurvature2475

/-  2482: explicit bridge from the generated cell table to the 2475 consumer.

The table is only data.  The analytic cell inequality remains the named
`hcell` premise below; this theorem prevents a later consumer from silently
changing the owner, sigma row, or cell indexing convention. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators

set_option linter.style.longLine false
set_option maxRecDepth 32768

theorem ownerPanelStripNorm_le_curvatureTableBridge2482
    (sigma radius step : ℝ) (side : Fin 2)
    (hradius : 0 ≤ radius)
    (hR : ∀ i : Fin 30, ownerRad_2463 i ≤ radius)
    (hstep : 0 < step)
    (hgrid : (640 : ℝ) * step = 2 * radius)
    (hcell : ∀ index ∈ Finset.range 640, ∀ coordinate ∈
      Set.Icc (-radius + index * step) (-radius + (index + 1) * step),
      ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) coordinate‖ ≤
        (ownerCurvatureQ_2481 side (Fin.ofNat 640 index) : ℝ)) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma radius step) step 640 +
        localCurvatureRemainder2474
          (fun index => (ownerCurvatureQ_2481 side (Fin.ofNat 640 index) : ℝ))
          step 640 := by
  apply ownerPanelStripNorm_le_localCurvature2475 sigma radius step 640
    (fun index => (ownerCurvatureQ_2481 side (Fin.ofNat 640 index) : ℝ))
    hradius hR hstep hgrid
  exact hcell

end ConnesWeilRH.Dev
