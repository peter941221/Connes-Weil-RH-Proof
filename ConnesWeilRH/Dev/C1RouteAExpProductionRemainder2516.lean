import ConnesWeilRH.Dev.C1RouteAExpUpperRemainder2515
import ConnesWeilRH.Dev.C1RouteAExpProductionPanel2514
import ConnesWeilRH.Dev.C1RouteAOwnerExpProduction2508

/-! Record 2516: instantiate the upper remainder interface on the certified
production safe range.  Cells outside 196..443 deliberately retain L1.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def ownerProductionSafe2516 : ℕ → Bool := fun index =>
  if 196 ≤ index ∧ index ≤ 443 then true else false

noncomputable def ownerProductionT2516 : ℕ → Fin 30 → ℝ := fun index i =>
    ownerCellEndpointRatio2488 stripRadius2303
      (stripRadius2303 / 320) index i

noncomputable def ownerProductionA2516 : ℕ → Fin 30 → ℝ := fun index i =>
    ownerCellLowerRatio2501 stripRadius2303
      (stripRadius2303 / 320) index i

noncomputable def ownerProductionCoefficientBound2516 : ℕ → Fin 30 → ℝ := fun _ i =>
    |(ownerCoef_2463 i).re| + |(ownerCoef_2463 i).im|

noncomputable def ownerProductionUpper2516 : ℕ → Fin 30 → ℝ := fun index i =>
    ownerProductionExpUpper2514 index i

noncomputable def ownerProductionRemainderTerm2516
    (sigma : ℝ) (index : ℕ) : ℝ :=
  if ownerProductionSafe2516 index = true then
    ownerExpUpperCurvatureSum2515 sigma ownerProductionT2516
      ownerProductionCoefficientBound2516 ownerProductionUpper2516 index
  else ownerWeightedCurvatureL1_2480 sigma stripRadius2303

set_option maxRecDepth 100000 in
theorem ownerPanelStripNorm_le_productionExpUpper2516
    (sigma : ℝ) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma stripRadius2303
          (stripRadius2303 / 320)) (stripRadius2303 / 320) 640 +
      localCurvatureRemainder2474 (ownerProductionRemainderTerm2516 sigma)
        (stripRadius2303 / 320) 640 := by
  unfold ownerProductionRemainderTerm2516
  have hR : ∀ i : Fin 30, ownerRad_2463 i ≤ stripRadius2303 := by
    intro i
    fin_cases i <;> norm_num [ownerRad_2463, rad0_2460, rad1_2460,
      rad2_2460, rad3_2460, rad4_2460, rad5_2460, rad6_2460, rad7_2460,
      rad8_2460, rad9_2460, rad10_2460, rad11_2460, rad12_2460,
      rad13_2460, rad14_2460, rad15_2460, rad16_2460, rad17_2460,
      rad18_2460, rad19_2460, rad20_2460, rad21_2460, rad22_2460,
      rad23_2460, rad24_2460, rad25_2460, rad26_2460, rad27_2460,
      rad28_2460, rad29_2460, stripRadius2303]
  apply ownerPanelStripNorm_le_expUpperCurvature2515 sigma stripRadius2303
    (stripRadius2303 / 320) 640 ownerProductionSafe2516 ownerProductionT2516
    ownerProductionA2516 ownerProductionCoefficientBound2516 ownerProductionUpper2516
  · norm_num [stripRadius2303]
  · exact hR
  · norm_num [stripRadius2303]
  · norm_num [stripRadius2303]
  · intro index hindex hsafe coordinate hcoordinate i
    have hsafe' : 196 ≤ index ∧ index ≤ 443 := by
      simpa [ownerProductionSafe2516] using hsafe
    have hs := (ownerCellSafeEndpoint_true_iff2488 stripRadius2303
      (stripRadius2303 / 320) index).mp
      (ownerCellSafeEndpoint_production2488 hsafe'.1 hsafe'.2)
    have hmax := abs_le_max_abs_endpoints_of_mem_Icc2488 hcoordinate
    exact lt_of_le_of_lt hmax (max_lt (hs i).1 (hs i).2)
  · intro index hindex hsafe coordinate hcoordinate i
    exact ownerCellEndpointRatio_nonneg2488 stripRadius2303
      (stripRadius2303 / 320) index i
  · intro index hindex hsafe coordinate hcoordinate i
    have hsafe' : 196 ≤ index ∧ index ≤ 443 := by
      simpa [ownerProductionSafe2516] using hsafe
    have hs := (ownerCellSafeEndpoint_true_iff2488 stripRadius2303
      (stripRadius2303 / 320) index).mp
      (ownerCellSafeEndpoint_production2488 hsafe'.1 hsafe'.2)
    exact ownerCellEndpointRatio_lt_one2488 stripRadius2303
      (stripRadius2303 / 320) index i (hs i).1 (hs i).2
  · intro index hindex hsafe coordinate hcoordinate i
    exact (ownerCoordinateNormalizedBound_of_endpointBound2488
      (fun j => ownerCellEndpointRatio2488 stripRadius2303
        (stripRadius2303 / 320) index j) hcoordinate
      (fun j => ownerCellEndpointRatio_endpointBound2488 stripRadius2303
        (stripRadius2303 / 320) index j)) i
  · intro index hindex hsafe coordinate hcoordinate i
    exact ownerCellLowerRatio_nonneg2501 stripRadius2303
      (stripRadius2303 / 320) index i
  · intro index hindex hsafe coordinate hcoordinate i
    have hsafe' : 196 ≤ index ∧ index ≤ 443 := by
      simpa [ownerProductionSafe2516] using hsafe
    exact ownerCellLowerRatio_lt_one_production2507 hsafe'.1 hsafe'.2 i
  · intro index hindex hsafe coordinate hcoordinate i
    have hstep : 0 ≤ stripRadius2303 / 320 := by
      norm_num [stripRadius2303]
    exact ownerCellLowerRatio_le_normalizedAbs2501 i
      (ownerRadPos_2465 i) hstep hcoordinate
  · intro index hindex i
    exact Complex.norm_le_abs_re_add_abs_im _
  · intro index hindex hsafe i
    have hsafe' : 196 ≤ index ∧ index ≤ 443 := by
      simpa [ownerProductionSafe2516] using hsafe
    simpa [ownerProductionUpper2516, ownerProductionExpUpper2514, neg_div] using
      ownerCellExpSplitUpper_production2508 hsafe'.1 hsafe'.2 i

end ConnesWeilRH.Dev
