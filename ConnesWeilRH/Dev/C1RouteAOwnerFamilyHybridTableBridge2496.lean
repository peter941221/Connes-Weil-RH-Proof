import ConnesWeilRH.Dev.C1RouteAOwnerFamilyHybridTable2496

/-  2496: bridge the corrected 2495 payload to the analytic hybrid consumer.
The table is data; the sole numerical premise is the per-cell analytic
inequality below the corresponding corrected rational payload. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

set_option linter.style.longLine false
set_option maxRecDepth 100000

noncomputable def ownerFamilyHybridTableRemainder2496
    (side : Fin 2) (step : ℝ) : ℝ :=
  localCurvatureRemainder2474
    (fun index => (ownerFamilyHybridQ_2496 side (Fin.ofNat 640 index) : ℝ))
    step 640

theorem ownerPanelStripNorm_le_familyHybridTable2496
    (sigma : ℝ) (side : Fin 2) (step : ℝ)
    (hcell : ∀ index ∈ Finset.range 640,
      ownerFamilyHybridCurvature2488 sigma stripRadius2303
        (stripRadius2303 / 320) index ≤
        (ownerFamilyHybridQ_2496 side (Fin.ofNat 640 index) : ℝ)) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma stripRadius2303
          (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
      ownerFamilyHybridTableRemainder2496 side (stripRadius2303 / 320) := by
  have hbase := ownerPanelStripNorm_le_productionFamilyHybridCurvature2488 sigma
  have hrem :
      localCurvatureRemainder2474
          (fun index => ownerFamilyHybridCurvature2488 sigma stripRadius2303
            (stripRadius2303 / 320) index)
          (stripRadius2303 / 320) 640 ≤
        ownerFamilyHybridTableRemainder2496 side (stripRadius2303 / 320) := by
    unfold ownerFamilyHybridTableRemainder2496 localCurvatureRemainder2474
    apply Finset.sum_le_sum
    intro index hindex
    have hpoint := hcell index hindex
    have hscale : 0 ≤ (stripRadius2303 / 320) ^ 3 / 12 := by
      norm_num [stripRadius2303]
    calc
      ownerFamilyHybridCurvature2488 sigma stripRadius2303
          (stripRadius2303 / 320) index * (stripRadius2303 / 320) ^ 3 / 12 =
        ownerFamilyHybridCurvature2488 sigma stripRadius2303
          (stripRadius2303 / 320) index * ((stripRadius2303 / 320) ^ 3 / 12) := by ring
      _ ≤ (ownerFamilyHybridQ_2496 side (Fin.ofNat 640 index) : ℝ) *
          ((stripRadius2303 / 320) ^ 3 / 12) :=
        mul_le_mul_of_nonneg_right hpoint hscale
      _ = (ownerFamilyHybridQ_2496 side (Fin.ofNat 640 index) : ℝ) *
          (stripRadius2303 / 320) ^ 3 / 12 := by ring
  calc
    stripNorm sigma ownerPanelSumValue_2467 ≤
        compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
          localCurvatureRemainder2474
            (fun index => ownerFamilyHybridCurvature2488 sigma stripRadius2303
              (stripRadius2303 / 320) index)
            (stripRadius2303 / 320) 640 := hbase
    _ = localCurvatureRemainder2474
          (fun index => ownerFamilyHybridCurvature2488 sigma stripRadius2303
            (stripRadius2303 / 320) index)
          (stripRadius2303 / 320) 640 +
        compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 := by ring
    _ ≤ ownerFamilyHybridTableRemainder2496 side (stripRadius2303 / 320) +
        compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 :=
      add_le_add hrem (le_refl _)
    _ = compositeNodeUpper2347
          (ownerPanelNodeUpper2471 sigma stripRadius2303
            (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
        ownerFamilyHybridTableRemainder2496 side (stripRadius2303 / 320) := by ring

end ConnesWeilRH.Dev
