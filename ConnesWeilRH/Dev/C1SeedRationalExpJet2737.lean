import ConnesWeilRH.Dev.C1SeedRationalPhaseBox2736

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable section

def rationalExpJet2737 (B : RealInterval2429) (m : ℕ) : ℕ → RealInterval2429 :=
  exponentialJetInterval2734 (phaseJetInterval2734 B)
    (rationalPhaseExpBox2736 (phaseJetInterval2734 B 0) m)

theorem rationalExpJet_mem2737 (B : RealInterval2429) (m N n : ℕ)
    (hm : 1 ≤ m) (hlo : 0 < B.lo) (hhi : B.hi < 1)
    (hP : (phaseJetInterval2734 B 0).hi ≤ 0)
    (hcap : -(phaseJetInterval2734 B 0).lo ≤ m)
    {x : ℝ} (hx : B.Mem x) (hn : n ≤ N) :
    (rationalExpJet2737 B m n).Mem (iteratedDeriv n transitionExp2731 x) := by
  have hphase := phaseJetInterval_mem2734 B 0 hlo hhi hx
  have he0 := rationalPhaseExpBox_mem2736
    (phaseJetInterval2734 B 0) m hm hP hcap hphase
  apply exponentialJetInterval_mem2734 (phaseJetInterval2734 B)
    (rationalPhaseExpBox2736 (phaseJetInterval2734 B 0) m) N
    (hlo.trans_le hx.1) (hx.2.trans_lt hhi) he0
    (fun j hj => phaseJetInterval_mem2734 B j hlo hhi hx) n hn

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
