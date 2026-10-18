import ConnesWeilRH.Dev.C1RouteBSharperExpInitialBox2856
import ConnesWeilRH.Dev.C1RouteBExponentialReplayBridge2848

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def routeBSharpExpReplay2859 : ℕ → RationalBox2744 :=
  rationalExponentialJet2750 routeBPhase2844 routeBSharperExpBox2856

def routeBSharpDenominator2859 : ℕ → RationalBox2744 :=
  fun n => if n = 0 then RationalBox2744.add (routeBSharpExpReplay2859 0)
    { lo := 1, hi := 1, ordered := by norm_num }
    else routeBSharpExpReplay2859 n

theorem routeB_sharp_exponential_replay_mem2859 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    ∀ n ≤ 7, (routeBSharpExpReplay2859 n).Mem
      (iteratedDeriv n transitionExp2731 x) := by
  exact routeB_exponential_replay_mem2848 routeBSharperExpBox2856
    (routeB_sharper_exp_initial_box_mem2856 hx) hx

theorem routeB_sharp_denominator_mem2859 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    ∀ n ≤ 7, (routeBSharpDenominator2859 n).Mem
      (iteratedDeriv n (fun y => 1 + transitionExp2731 y) x) := by
  have hlo : 0 < routeBCell4096Interval2845.lo := by
    norm_num [routeBCell4096Interval2845]
  have hhi : routeBCell4096Interval2845.hi < 1 := by
    norm_num [routeBCell4096Interval2845]
  have hexp := routeB_sharp_exponential_replay_mem2859 hx
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [routeBSharpDenominator2859, if_pos rfl, iteratedDeriv_zero]
    have hone : ({ lo := (1 : ℚ), hi := 1, ordered := by norm_num } :
        RationalBox2744).Mem (1 : ℝ) := by
      simp [RationalBox2744.Mem]
    have hsum := RationalBox2744.mem_add (hexp 0 (by omega)) hone
    simpa [add_comm] using hsum
  · rw [routeBSharpDenominator2859, if_neg hn0,
      iteratedDeriv_const_add (Nat.pos_of_ne_zero hn0)]
    simpa using hexp n hn

end
end ConnesWeilRH.Dev
