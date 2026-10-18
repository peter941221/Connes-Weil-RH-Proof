import ConnesWeilRH.Dev.C1RouteBSharpNormCharge2862

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def routeBSharpCellWidth2863 : ℝ := (2047 : ℝ) / 33554432

def routeBSharpCellCharge2863 (n : ℕ) : ℝ :=
  4 * routeBSharpCellWidth2863 *
    routeBSharpAbsMax2862
      (rationalTransitionJet2749 routeBSharpExpReplay2859
        routeBSharpReciprocal2860 n)

theorem routeB_sharp_cell_charge_bound2863 (n : ℕ) :
    routeBSharpCellWidth2863 *
      routeBSharpAbsMax2862
        (rationalTransitionJet2749 routeBSharpExpReplay2859
          routeBSharpReciprocal2860 n) ≤ routeBSharpCellCharge2863 n := by
  unfold routeBSharpCellCharge2863
  have hnonneg : 0 ≤ routeBSharpCellWidth2863 := by
    norm_num [routeBSharpCellWidth2863]
  have hmax : 0 ≤ routeBSharpAbsMax2862
      (rationalTransitionJet2749 routeBSharpExpReplay2859
        routeBSharpReciprocal2860 n) := by
    unfold routeBSharpAbsMax2862
    positivity
  nlinarith

theorem routeB_sharp_d4d7_cell_charge_bound2863 :
    routeBSharpCellWidth2863 *
        routeBSharpAbsMax2862
          (rationalTransitionJet2749 routeBSharpExpReplay2859
            routeBSharpReciprocal2860 4) ≤ routeBSharpCellCharge2863 4 ∧
      routeBSharpCellWidth2863 *
        routeBSharpAbsMax2862
          (rationalTransitionJet2749 routeBSharpExpReplay2859
            routeBSharpReciprocal2860 7) ≤ routeBSharpCellCharge2863 7 := by
  exact ⟨routeB_sharp_cell_charge_bound2863 4,
    routeB_sharp_cell_charge_bound2863 7⟩

end
end ConnesWeilRH.Dev
