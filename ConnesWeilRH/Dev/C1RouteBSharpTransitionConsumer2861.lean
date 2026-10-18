import ConnesWeilRH.Dev.C1RouteBSharpExpDenominator2859
import ConnesWeilRH.Dev.C1RouteBSharpReciprocal2860
import ConnesWeilRH.Dev.C1RationalTransitionJet2749

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

theorem routeB_sharp_transition_mem2861 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    ∀ n ≤ 7,
      (rationalTransitionJet2749 routeBSharpExpReplay2859
        routeBSharpReciprocal2860 n).Mem
        (iteratedDeriv n Real.smoothTransition x) := by
  have hlo : 0 < routeBCell4096Interval2845.lo := by
    norm_num [routeBCell4096Interval2845]
  have hhi : routeBCell4096Interval2845.hi < 1 := by
    norm_num [routeBCell4096Interval2845]
  have hexp := routeB_sharp_exponential_replay_mem2859 hx
  have hrec := routeB_sharp_reciprocal_mem2860 hx
  intro n hn
  exact rationalTransitionJet_mem2749 routeBSharpExpReplay2859
    routeBSharpReciprocal2860 n (hlo.trans_le hx.1) (hx.2.trans_lt hhi)
    (fun j hj => hexp j (by omega)) (fun j hj => hrec j (by omega))

end
end ConnesWeilRH.Dev
