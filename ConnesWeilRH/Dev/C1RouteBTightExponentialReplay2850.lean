import ConnesWeilRH.Dev.C1RouteBExponentialReplayBridge2848
import ConnesWeilRH.Dev.C1RouteBExpInitialBox2849

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

theorem routeB_tight_exponential_replay_mem2850 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    ∀ n ≤ 7,
      (rationalExponentialJet2750 routeBPhase2844
        routeBExpInitialBox2849 n).Mem
        (iteratedDeriv n transitionExp2731 x) := by
  exact routeB_exponential_replay_mem2848 routeBExpInitialBox2849
    (routeB_exp_initial_box_mem2849 hx) hx

end
end ConnesWeilRH.Dev
