import ConnesWeilRH.Dev.C1RationalNegativeExp2735
import ConnesWeilRH.Dev.C1SeedIntervalJet2734

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable section

def rationalPhaseExpBox2736 (P : RealInterval2429) (m : ℕ) : RealInterval2429 :=
  { lo := ((expTaylor (-P.lo / m) + expTail (-P.lo / m)) ^ m)⁻¹
    hi := ((expTaylor (-P.hi / m) - expTail (-P.hi / m)) ^ m)⁻¹ }

theorem rationalPhaseExpBox_mem2736 (P : RealInterval2429) (m : ℕ)
    (hm : 1 ≤ m) (hP : P.hi ≤ 0) (hcap : -P.lo ≤ m)
    {z : ℝ} (hz : P.Mem z) :
    (rationalPhaseExpBox2736 P m).Mem (Real.exp z) := by
  have hw : 0 ≤ -P.lo := by linarith [hz.1, hz.2, hP]
  have hboxLo := rational_negative_exp_box2735 hw m hm hcap
  have hwHi : 0 ≤ -P.hi := by linarith [hP]
  have hcapHi : -P.hi ≤ m := by linarith [hcap, hz.1, hz.2]
  have hboxHi := rational_negative_exp_box2735 hwHi m hm hcapHi
  have hzlo : -(-P.lo) ≤ z := by simpa using hz.1
  have hzhi : z ≤ -(-P.hi) := by simpa using hz.2
  constructor
  · simpa only [neg_neg] using hboxLo.1.trans (Real.exp_le_exp.mpr hzlo)
  · simpa only [rationalPhaseExpBox2736, neg_neg] using
      (Real.exp_le_exp.mpr hzhi).trans hboxHi.2

def representativeCell2736 : RealInterval2429 :=
  { lo := 2049 / 8192, hi := 8394751 / 33554432 }

theorem representativePhaseExpBox_mem2736 {x : ℝ}
    (hx : representativeCell2736.Mem x) :
    (rationalPhaseExpBox2736 (phaseJetInterval2734 representativeCell2736 0) 4).Mem
      (Real.exp (transitionPhase2731 x)) := by
  have hp := phaseJetInterval_mem2734 representativeCell2736 0
    (by norm_num [representativeCell2736]) (by norm_num [representativeCell2736]) hx
  have hP : (phaseJetInterval2734 representativeCell2736 0).hi ≤ 0 := by
    have h := hp.2
    rw [show (phaseJetInterval2734 representativeCell2736 0).hi =
      (1 - representativeCell2736.hi)⁻¹ - representativeCell2736.hi⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
        coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [representativeCell2736]
  have hcap : -(phaseJetInterval2734 representativeCell2736 0).lo ≤ (4 : ℝ) := by
    rw [show (phaseJetInterval2734 representativeCell2736 0).lo =
      (1 - representativeCell2736.lo)⁻¹ - representativeCell2736.lo⁻¹ by
      simp [phaseJetInterval2734, reciprocalJetInterval2734, reflectedCoordinateJetInterval2734,
        coordinateJetInterval2734, RealInterval2429.sub, RealInterval2429.invPositive,
        RealInterval2429.point]]
    norm_num [representativeCell2736]
  exact rationalPhaseExpBox_mem2736 (phaseJetInterval2734 representativeCell2736 0) 4
    (by norm_num) hP hcap hp

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
