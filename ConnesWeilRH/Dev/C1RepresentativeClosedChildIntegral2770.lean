import ConnesWeilRH.Dev.C1RealIntervalIntegralEnvelope2769
import ConnesWeilRH.Dev.C1RepresentativeClosedChildD4D72768

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev
noncomputable section

def leftChildD4Box2770 : RealInterval2429 :=
  rationalSeedTransitionJet2738 leftCell2740 4 4

def leftChildD7Box2770 : RealInterval2429 :=
  rationalSeedTransitionJet2738 leftCell2740 4 7

def rightChildD4Box2770 : RealInterval2429 :=
  rationalSeedTransitionJet2738 rightCell2740 4 4

def rightChildD7Box2770 : RealInterval2429 :=
  rationalSeedTransitionJet2738 rightCell2740 4 7

theorem leftChildD4D7_integral_bounds2770 :
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        (leftCell2740.hi - leftCell2740.lo) * leftChildD4Box2770.endpointAbsMax ∧
    (∫ x in leftCell2740.lo..leftCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        (leftCell2740.hi - leftCell2740.lo) * leftChildD7Box2770.endpointAbsMax := by
  have hcont4 := (contDiff_one_iteratedDeriv_smoothTransition 4).continuous
  have hcont7 := (contDiff_one_iteratedDeriv_smoothTransition 7).continuous
  have h4 := intervalIntegral_norm_le_endpointAbsMax2769
    (show leftCell2740.lo ≤ leftCell2740.hi by norm_num [leftCell2740, representativeCell2736])
    leftChildD4Box2770 hcont4 (fun x hx =>
      (leftClosedChildD4D7_mem2768 (show leftCell2740.Mem x from hx)).1)
  have h7 := intervalIntegral_norm_le_endpointAbsMax2769
    (show leftCell2740.lo ≤ leftCell2740.hi by norm_num [leftCell2740, representativeCell2736])
    leftChildD7Box2770 hcont7 (fun x hx =>
      (leftClosedChildD4D7_mem2768 (show leftCell2740.Mem x from hx)).2)
  exact ⟨h4, h7⟩

theorem rightChildD4D7_integral_bounds2770 :
    (∫ x in rightCell2740.lo..rightCell2740.hi,
      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤
        (rightCell2740.hi - rightCell2740.lo) * rightChildD4Box2770.endpointAbsMax ∧
    (∫ x in rightCell2740.lo..rightCell2740.hi,
      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤
        (rightCell2740.hi - rightCell2740.lo) * rightChildD7Box2770.endpointAbsMax := by
  have hcont4 := (contDiff_one_iteratedDeriv_smoothTransition 4).continuous
  have hcont7 := (contDiff_one_iteratedDeriv_smoothTransition 7).continuous
  have h4 := intervalIntegral_norm_le_endpointAbsMax2769
    (show rightCell2740.lo ≤ rightCell2740.hi by norm_num [rightCell2740, representativeCell2736])
    rightChildD4Box2770 hcont4 (fun x hx =>
      (rightClosedChildD4D7_mem2768 (show rightCell2740.Mem x from hx)).1)
  have h7 := intervalIntegral_norm_le_endpointAbsMax2769
    (show rightCell2740.lo ≤ rightCell2740.hi by norm_num [rightCell2740, representativeCell2736])
    rightChildD7Box2770 hcont7 (fun x hx =>
      (rightClosedChildD4D7_mem2768 (show rightCell2740.Mem x from hx)).2)
  exact ⟨h4, h7⟩

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
