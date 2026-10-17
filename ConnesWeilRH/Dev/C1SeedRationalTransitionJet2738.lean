import ConnesWeilRH.Dev.C1SeedRationalExpJet2737

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable section

def rationalSeedDenominatorJet2738 (B : RealInterval2429) (m n : ℕ) : RealInterval2429 :=
  (RealInterval2429.point (if n = 0 then 1 else 0)).add (rationalExpJet2737 B m n)

def rationalSeedTransitionJet2738 (B : RealInterval2429) (m n : ℕ) : RealInterval2429 :=
  productJetInterval2734 (rationalExpJet2737 B m)
    (reciprocalJetInterval2734 (rationalSeedDenominatorJet2738 B m)) n

theorem rationalSeedExpJet_mem2738 (B : RealInterval2429) (m n : ℕ)
    (hm : 1 ≤ m) (hlo : 0 < B.lo) (hhi : B.hi < 1)
    (hP : (phaseJetInterval2734 B 0).hi ≤ 0)
    (hcap : -(phaseJetInterval2734 B 0).lo ≤ m)
    {x : ℝ} (hx : B.Mem x) :
    (rationalExpJet2737 B m n).Mem (iteratedDeriv n transitionExp2731 x) := by
  exact rationalExpJet_mem2737 B m n n hm hlo hhi hP hcap hx le_rfl

theorem rationalSeedDenominatorJet_mem2738 (B : RealInterval2429) (m n : ℕ)
    (hm : 1 ≤ m) (hlo : 0 < B.lo) (hhi : B.hi < 1)
    (hP : (phaseJetInterval2734 B 0).hi ≤ 0)
    (hcap : -(phaseJetInterval2734 B 0).lo ≤ m)
    {x : ℝ} (hx : B.Mem x) :
    (rationalSeedDenominatorJet2738 B m n).Mem
      (iteratedDeriv n (fun y => 1 + transitionExp2731 y) x) := by
  have h := RealInterval2429.mem_add (RealInterval2429.point_mem (if n = 0 then 1 else 0))
    (rationalSeedExpJet_mem2738 B m n hm hlo hhi hP hcap hx)
  by_cases hn : n = 0
  · subst n
    simpa only [iteratedDeriv_zero, ite_true] using h
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hn) 1]
    simpa only [rationalSeedDenominatorJet2738, if_neg hn, zero_add] using h

theorem rationalSeedReciprocalJet_mem2738 (B : RealInterval2429) (m n : ℕ)
    (hm : 1 ≤ m) (hlo : 0 < B.lo) (hhi : B.hi < 1)
    (hP : (phaseJetInterval2734 B 0).hi ≤ 0)
    (hcap : -(phaseJetInterval2734 B 0).lo ≤ m)
    {x : ℝ} (hx : B.Mem x) :
    (reciprocalJetInterval2734 (rationalSeedDenominatorJet2738 B m) n).Mem
      (iteratedDeriv n transitionReciprocal2731 x) := by
  have hdenlo : 0 < (rationalSeedDenominatorJet2738 B m 0).lo := by
    change 0 < 1 + (rationalExpJet2737 B m 0).lo
    have hphase := phaseJetInterval_mem2734 B 0 hlo hhi hx
    have hplo : (phaseJetInterval2734 B 0).lo ≤ 0 :=
      le_trans hphase.1 (le_trans hphase.2 hP)
    have hEpos : 0 < (rationalExpJet2737 B m 0).lo := by
      unfold rationalExpJet2737 exponentialJetInterval2734 rationalPhaseExpBox2736
      change 0 < ((expTaylor (-(phaseJetInterval2734 B 0).lo / m) +
        expTail (-(phaseJetInterval2734 B 0).lo / m)) ^ m)⁻¹
      have hneg : 0 ≤ -(phaseJetInterval2734 B 0).lo := neg_nonneg.mpr hplo
      have hw : 0 ≤ -(phaseJetInterval2734 B 0).lo / m := by positivity
      have ht := one_le_expTaylor hw
      have hr : 0 ≤ expTail (-(phaseJetInterval2734 B 0).lo / m) := by
        unfold expTail
        positivity
      have hq : 0 < expTaylor (-(phaseJetInterval2734 B 0).lo / m) +
          expTail (-(phaseJetInterval2734 B 0).lo / m) := by linarith
      exact inv_pos.mpr (pow_pos hq m)
    linarith
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => 1 + transitionExp2731 y) x :=
    contDiffAt_const.add (contDiffAt_transitionExp2731 ⊤
      (hlo.trans_le hx.1) (hx.2.trans_lt hhi))
  exact reciprocalJetInterval_mem2734 (rationalSeedDenominatorJet2738 B m)
    (fun y => 1 + transitionExp2731 y) n hf hdenlo
    (fun j _ => rationalSeedDenominatorJet_mem2738 B m j hm hlo hhi hP hcap hx)
    n le_rfl

theorem rationalSeedTransitionJet_mem2738 (B : RealInterval2429) (m n : ℕ)
    (hm : 1 ≤ m) (hlo : 0 < B.lo) (hhi : B.hi < 1)
    (hP : (phaseJetInterval2734 B 0).hi ≤ 0)
    (hcap : -(phaseJetInterval2734 B 0).lo ≤ m)
    {x : ℝ} (hx : B.Mem x) :
    (rationalSeedTransitionJet2738 B m n).Mem
      (iteratedDeriv n Real.smoothTransition x) := by
  rw [iteratedDeriv_smoothTransition_product2731 n
    (hlo.trans_le hx.1) (hx.2.trans_lt hhi)]
  exact productJetInterval_mem2734 (rationalExpJet2737 B m)
    (reciprocalJetInterval2734 (rationalSeedDenominatorJet2738 B m)) n
    (fun j => iteratedDeriv j transitionExp2731 x)
    (fun j => iteratedDeriv j transitionReciprocal2731 x)
    (fun j _ => rationalSeedExpJet_mem2738 B m j hm hlo hhi hP hcap hx)
    (fun j _ => rationalSeedReciprocalJet_mem2738 B m j hm hlo hhi hP hcap hx)

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
