import ConnesWeilRH.Dev.C1RouteBFiniteTargetAssembly2812

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_split_d4d7_target_2813
    {finite4 tail4 finite7 tail7 : ℝ}
    (hfinite4 : finite4 < 1500)
    (hfinite7 : finite7 < 2000000000)
    (htail4 : 0 ≤ tail4)
    (htail7 : 0 ≤ tail7)
    (htarget4 : finite4 + tail4 < 61000000)
    (htarget7 : finite7 + tail7 < 2000000000) :
    finite4 + tail4 < 61000000 ∧
      finite7 + tail7 < 2000000000 := by
  exact ⟨htarget4, htarget7⟩

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
