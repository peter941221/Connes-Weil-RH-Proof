import ConnesWeilRH.Dev.C1RouteBSharpExpDenominator2859
import ConnesWeilRH.Dev.C1RationalReciprocalJet2748

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Source.C1ExplicitSmoothSeed
noncomputable section

def routeBSharpReciprocal2860 : ℕ → RationalBox2744 :=
  rationalReciprocalJet2748 routeBSharpDenominator2859 (by
    have h : 0 < (routeBSharpExpReplay2859 0).lo := by
      norm_num [routeBSharpExpReplay2859, rationalExponentialJet2750,
        routeBPhase2844, routeBSharperExpBox2856, RationalBox2744.sum,
        RationalBox2744.zero, RationalBox2744.add, RationalBox2744.mul,
        RationalBox2744.nsmul]
    simpa [routeBSharpDenominator2859] using add_pos h (by norm_num : (0 : ℚ) < 1))

theorem routeB_sharp_reciprocal_mem2860 {x : ℝ}
    (hx : routeBCell4096Interval2845.Mem x) :
    ∀ n ≤ 7, (routeBSharpReciprocal2860 n).Mem
      (iteratedDeriv n transitionReciprocal2731 x) := by
  have hlo : 0 < routeBCell4096Interval2845.lo := by
    norm_num [routeBCell4096Interval2845]
  have hhi : routeBCell4096Interval2845.hi < 1 := by
    norm_num [routeBCell4096Interval2845]
  exact rationalReciprocalJet_mem2748 routeBSharpDenominator2859 (by
      have h : 0 < (routeBSharpExpReplay2859 0).lo := by
        norm_num [routeBSharpExpReplay2859, rationalExponentialJet2750,
          routeBPhase2844, routeBSharperExpBox2856, RationalBox2744.sum,
          RationalBox2744.zero, RationalBox2744.add, RationalBox2744.mul,
          RationalBox2744.nsmul]
      simpa [routeBSharpDenominator2859] using
        add_pos h (by norm_num : (0 : ℚ) < 1)) (fun y => 1 + transitionExp2731 y) 7
    (contDiffAt_const.add (contDiffAt_transitionExp2731 ⊤
      (hlo.trans_le hx.1) (hx.2.trans_lt hhi)))
    (routeB_sharp_denominator_mem2859 hx)
    (by
      have he : 0 < transitionExp2731 x := by
        unfold transitionExp2731
        exact Real.exp_pos _
      linarith)

end
end ConnesWeilRH.Dev
