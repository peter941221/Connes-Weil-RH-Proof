import ConnesWeilRH.Dev.C1RouteAExpProductionTable2519

/-! 2521: repair the production fallback's pricing convention.

The historical 2516 term uses one global exponential weight outside the safe
range. The 2517 price instead sums family-supported weighted bounds. This
module proves that tighter fallback for the same function, including support
edges, and attaches it to the actual production remainder. The old definition
and its conditional table theorem remain unchanged.
-/

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

set_option maxRecDepth 100000

theorem ownerPanelWeightedSecondDeriv_le_familyFallback2521 (sigma x : ℝ) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ownerFamilyL1SumCurvature2488 sigma := by
  exact ownerPanelWeightedSecondDeriv_le_sumFamilyBound2488 sigma x
    (ownerFamilyWeightedCurvatureL1_2488 sigma)
    (ownerFamilyWeightedSecondDerivBoundL1_2488 sigma x)

noncomputable def ownerProductionRemainderTerm2521 (sigma : ℝ) (index : ℕ) : ℝ :=
  if ownerProductionSafe2516 index = true then
    ownerExpUpperCurvatureSum2515 sigma ownerProductionT2516
      ownerProductionCoefficientBound2516 ownerProductionUpper2516 index
  else ownerFamilyL1SumCurvature2488 sigma

theorem ownerProductionCell_bound2521 (sigma x : ℝ) (index : ℕ)
    (hx : x ∈ Set.Icc
      (-stripRadius2303 + index * (stripRadius2303 / 320))
      (-stripRadius2303 + (index + 1) * (stripRadius2303 / 320))) :
    ‖deriv (deriv (weightedFunction2348 sigma ownerPanelSumValue_2467)) x‖ ≤
      ownerProductionRemainderTerm2521 sigma index := by
  unfold ownerProductionRemainderTerm2521
  split_ifs with hs
  · have hs' : 196 ≤ index ∧ index ≤ 443 := by
      simpa [ownerProductionSafe2516] using hs
    exact ownerPanelProductionExpUpper_safeCell2514 sigma x index hs'.1 hs'.2 hx
  · exact ownerPanelWeightedSecondDeriv_le_familyFallback2521 sigma x

set_option maxRecDepth 100000 in
theorem ownerPanelStripNorm_le_productionExpUpper2521 (sigma : ℝ) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma stripRadius2303 (stripRadius2303 / 320))
        (stripRadius2303 / 320) 640 +
      localCurvatureRemainder2474 (ownerProductionRemainderTerm2521 sigma)
        (stripRadius2303 / 320) 640 := by
  apply ownerPanelStripNorm_le_localCurvature2475 sigma stripRadius2303
    (stripRadius2303 / 320) 640 (ownerProductionRemainderTerm2521 sigma)
  · norm_num [stripRadius2303]
  · intro i
    fin_cases i <;> norm_num [ownerRad_2463, stripRadius2303,
      rad0_2460, rad1_2460, rad2_2460, rad3_2460, rad4_2460, rad5_2460,
      rad6_2460, rad7_2460, rad8_2460, rad9_2460, rad10_2460, rad11_2460,
      rad12_2460, rad13_2460, rad14_2460, rad15_2460, rad16_2460, rad17_2460,
      rad18_2460, rad19_2460, rad20_2460, rad21_2460, rad22_2460, rad23_2460,
      rad24_2460, rad25_2460, rad26_2460, rad27_2460, rad28_2460, rad29_2460]
  · norm_num [stripRadius2303]
  · norm_num [stripRadius2303]
  · intro index _ x hx
    exact ownerProductionCell_bound2521 sigma x index hx

theorem ownerPanelStripNorm_le_productionTable2521
    (sigma : ℝ) (table : ℕ → ℝ)
    (hcell : ∀ index ∈ Finset.range 640,
      ownerProductionRemainderTerm2521 sigma index ≤ table index) :
    stripNorm sigma ownerPanelSumValue_2467 ≤
      compositeNodeUpper2347
        (ownerPanelNodeUpper2471 sigma stripRadius2303 (stripRadius2303 / 320))
        (stripRadius2303 / 320) 640 +
      localCurvatureRemainder2474 table (stripRadius2303 / 320) 640 := by
  apply (ownerPanelStripNorm_le_productionExpUpper2521 sigma).trans
  refine add_le_add (le_refl _) ?_
  unfold localCurvatureRemainder2474
  apply Finset.sum_le_sum
  intro index hi
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hcell index hi)
      (by norm_num [stripRadius2303])) (by norm_num)

end ConnesWeilRH.Dev
