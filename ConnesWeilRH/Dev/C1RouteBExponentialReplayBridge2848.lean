import ConnesWeilRH.Dev.C1RouteBPhaseBoxBridge2845
import ConnesWeilRH.Dev.C1RationalExponentialJet2750

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

theorem routeB_exponential_replay_mem2848
    {x : ℝ} (e0 : RationalBox2744) (he0 : e0.Mem (transitionExp2731 x))
    (hx : routeBCell4096Interval2845.Mem x) :
    ∀ n ≤ 7, (rationalExponentialJet2750 routeBPhase2844 e0 n).Mem
      (iteratedDeriv n transitionExp2731 x) := by
  have hlo : 0 < routeBCell4096Interval2845.lo := by
    norm_num [routeBCell4096Interval2845]
  have hhi : routeBCell4096Interval2845.hi < 1 := by
    norm_num [routeBCell4096Interval2845]
  apply rationalExponentialJet_mem2750 routeBPhase2844 e0 7
    (hlo.trans_le hx.1) (hx.2.trans_lt hhi) he0
  intro j hj
  have hphase := phaseJetInterval_mem2734 routeBCell4096Interval2845 j hlo hhi hx
  have hbox := routeB_phase_box_contains_lean_interval2845 j hj
  exact ⟨le_trans (show (routeBPhase2844 j).lo ≤
      (phaseJetInterval2734 routeBCell4096Interval2845 j).lo from hbox.1) hphase.1,
    le_trans hphase.2 hbox.2⟩

end
end ConnesWeilRH.Dev
