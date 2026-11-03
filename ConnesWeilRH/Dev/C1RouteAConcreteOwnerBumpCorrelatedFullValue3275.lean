import ConnesWeilRH.Dev.C1RouteAConcreteOwnerBumpCorrelatedPhaseBlocks3272

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell16923BumpCorrelatedFullRect3275 : ComplexRect2427 :=
  ((((record2680Cell16923BumpCorrelatedBlock0to4Rect3272.add
      record2680Cell16923BumpCorrelatedBlock5to9Rect3272).add
      record2680Cell16923BumpCorrelatedBlock10to14Rect3272).add
      record2680Cell16923BumpCorrelatedBlock15to19Rect3272).add
      record2680Cell16923BumpCorrelatedBlock20to24Rect3272).add
      record2680Cell16923BumpCorrelatedBlock25to29Rect3272

theorem record2680_cell16923_bump_correlated_full_reHi_decomposition3275 :
    record2680Cell16923BumpCorrelatedFullRect3275.reHi =
      record2680Cell16923BumpCorrelatedBlock0to4Rect3272.reHi +
      record2680Cell16923BumpCorrelatedBlock5to9Rect3272.reHi +
      record2680Cell16923BumpCorrelatedBlock10to14Rect3272.reHi +
      record2680Cell16923BumpCorrelatedBlock15to19Rect3272.reHi +
      record2680Cell16923BumpCorrelatedBlock20to24Rect3272.reHi +
      record2680Cell16923BumpCorrelatedBlock25to29Rect3272.reHi := by
  rfl

theorem record2680_cell16923_bump_correlated_full_reHi_le_of_block_bounds3275
    {u0 u1 u2 u3 u4 u5 : ℝ}
    (h0 : record2680Cell16923BumpCorrelatedBlock0to4Rect3272.reHi ≤ u0)
    (h1 : record2680Cell16923BumpCorrelatedBlock5to9Rect3272.reHi ≤ u1)
    (h2 : record2680Cell16923BumpCorrelatedBlock10to14Rect3272.reHi ≤ u2)
    (h3 : record2680Cell16923BumpCorrelatedBlock15to19Rect3272.reHi ≤ u3)
    (h4 : record2680Cell16923BumpCorrelatedBlock20to24Rect3272.reHi ≤ u4)
    (h5 : record2680Cell16923BumpCorrelatedBlock25to29Rect3272.reHi ≤ u5) :
    record2680Cell16923BumpCorrelatedFullRect3275.reHi ≤
      u0 + u1 + u2 + u3 + u4 + u5 := by
  rw [record2680_cell16923_bump_correlated_full_reHi_decomposition3275]
  linarith

end ConnesWeilRH.Dev
