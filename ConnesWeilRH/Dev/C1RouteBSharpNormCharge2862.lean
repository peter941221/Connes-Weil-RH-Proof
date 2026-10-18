import ConnesWeilRH.Dev.C1RouteBSharpTransitionConsumer2861

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def routeBSharpAbsMax2862 (b : RationalBox2744) : ℝ :=
  max |(b.lo : ℝ)| |(b.hi : ℝ)|

theorem routeB_sharp_norm_le_abs_max2862 {b : RationalBox2744} {v : ℝ}
    (hv : b.Mem v) : |v| ≤ routeBSharpAbsMax2862 b := by
  exact abs_le_max_abs_abs hv.1 hv.2

theorem routeB_sharp_norm_bound2862 {x : ℝ} (hx : routeBCell4096Interval2845.Mem x)
    (n : ℕ) (hn : n ≤ 7) :
    ‖iteratedDeriv n Real.smoothTransition x‖ ≤
      routeBSharpAbsMax2862
        (rationalTransitionJet2749 routeBSharpExpReplay2859
          routeBSharpReciprocal2860 n) := by
  rw [Real.norm_eq_abs]
  exact routeB_sharp_norm_le_abs_max2862
    (routeB_sharp_transition_mem2861 hx n hn)

end
end ConnesWeilRH.Dev
