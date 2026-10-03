import ConnesWeilRH.Dev.C1RouteAExpProductionRemainder2516

/-! 2518: expose the production exponential remainder to a certified table.

The table is deliberately an abstract payload.  The bridge keeps the
per-cell inequality as an explicit premise and only uses monotonicity of the
nonnegative local-curvature remainder weights.  External prices are not
imported as Lean facts here.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

set_option linter.style.longLine false
set_option maxRecDepth 100000

noncomputable def ownerProductionExpUpperTableRemainder2518
    (table : ℕ → ℝ) (step : ℝ) : ℝ :=
  localCurvatureRemainder2474 table step 640

theorem ownerPanelStripNorm_le_productionExpUpperTable2518
    (sigma : ℝ)
    (table : ℕ → ℝ)
    (hcell : ∀ index ∈ Finset.range 640,
      ownerProductionRemainderTerm2516 sigma index ≤ table index) :
      stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma stripRadius2303
          (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
      ownerProductionExpUpperTableRemainder2518 table
        (stripRadius2303 / 320) := by
  have hbase := ownerPanelStripNorm_le_productionExpUpper2516 sigma
  have hrem :
      localCurvatureRemainder2474 (ownerProductionRemainderTerm2516 sigma)
          (stripRadius2303 / 320) 640 ≤
        ownerProductionExpUpperTableRemainder2518 table
          (stripRadius2303 / 320) := by
    unfold ownerProductionExpUpperTableRemainder2518 localCurvatureRemainder2474
    apply Finset.sum_le_sum
    intro index hindex
    have hpoint := hcell index hindex
    have hscale : 0 ≤ (stripRadius2303 / 320) ^ 3 / 12 := by
      norm_num [stripRadius2303]
    calc
      ownerProductionRemainderTerm2516 sigma index *
          (stripRadius2303 / 320) ^ 3 / 12 =
          ownerProductionRemainderTerm2516 sigma index *
            ((stripRadius2303 / 320) ^ 3 / 12) := by ring
      _ ≤ table index * ((stripRadius2303 / 320) ^ 3 / 12) :=
        mul_le_mul_of_nonneg_right hpoint hscale
      _ = table index * (stripRadius2303 / 320) ^ 3 / 12 := by ring
  calc
    stripNorm sigma ownerPanelSumValue_2467 ≤
        compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
          localCurvatureRemainder2474
            (ownerProductionRemainderTerm2516 sigma)
            (stripRadius2303 / 320) 640 := hbase
    _ = localCurvatureRemainder2474
          (ownerProductionRemainderTerm2516 sigma)
          (stripRadius2303 / 320) 640 +
        compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 := by ring
    _ ≤ ownerProductionExpUpperTableRemainder2518 table
          (stripRadius2303 / 320) +
        compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 :=
      add_le_add hrem (le_refl _)
    _ = compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
        ownerProductionExpUpperTableRemainder2518 table
          (stripRadius2303 / 320) := by ring

end ConnesWeilRH.Dev
