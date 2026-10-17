import ConnesWeilRH.Dev.C1SeedRationalPhaseBox2736

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed
open ConnesWeilRH.Dev
noncomputable section

 theorem rationalPhaseExpBox_lo_pos2742 (P : RealInterval2429) (m : ℕ)
    (hm : 1 ≤ m) (hlo : 0 ≤ -P.lo) (hcap : -P.lo ≤ m) :
    0 < (rationalPhaseExpBox2736 P m).lo := by
  unfold rationalPhaseExpBox2736
  have hw : 0 ≤ -P.lo / m := by positivity
  have ht := one_le_expTaylor hw
  have hr : 0 ≤ expTail (-P.lo / m) := by
    unfold expTail
    positivity
  have hq : 0 < expTaylor (-P.lo / m) + expTail (-P.lo / m) := by
    linarith
  exact inv_pos.mpr (pow_pos hq m)

theorem rationalPhaseExpBox_hi_pos2742 (P : RealInterval2429) (m : ℕ)
    (hm : 1 ≤ m) (hhi : 0 ≤ -P.hi) (hcap : -P.hi ≤ m) :
    0 < (rationalPhaseExpBox2736 P m).hi := by
  unfold rationalPhaseExpBox2736
  have hw : 0 ≤ -P.hi / m := by positivity
  have hw1 : -P.hi / m ≤ 1 := by
    exact (div_le_one (by positivity)).mpr hcap
  have hp := one_le_expTaylor_sub_expTail hw hw1
  exact inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hp) m)

theorem rationalPhaseExpBox_ordered2742 (P : RealInterval2429) (m : ℕ)
    {z : ℝ} (hz : P.Mem z) (hm : 1 ≤ m) (hP : P.hi ≤ 0)
    (hcap : -P.lo ≤ m) :
    (rationalPhaseExpBox2736 P m).lo ≤
      (rationalPhaseExpBox2736 P m).hi := by
  have hmem := rationalPhaseExpBox_mem2736 P m hm hP hcap hz
  exact hmem.1.trans hmem.2

end
end ConnesWeilRH.Source.C1ExplicitSmoothSeed
