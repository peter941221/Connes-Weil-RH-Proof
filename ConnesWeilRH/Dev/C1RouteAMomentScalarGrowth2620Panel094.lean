import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentScalarGrowth2620Input : RatPair2542 := (momentPanelGrowth2620 / (2 : ℚ) ^ 20, 0)

def momentScalarGrowth2620Expected : RatState2542 :=
  ((((1127636935500616193526888959845344426103550507120774913675478548668058289092031677236322794630559 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1429449564045497479970401322720600533176975009663 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrowth2620_replay :
    compactExp2620 momentScalarGrowth2620Input 20 = momentScalarGrowth2620Expected := by
  decide +kernel

theorem momentScalarGrowth2620_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) (1 / 200) * (1 / 200)) - (momentScalarGrowth2620Expected.1.1 : ℝ)| ≤
      (momentScalarGrowth2620Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2620 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2620]
  have h := compactExp_real_error2620 momentPanelGrowth2620 20 hsmall
  change |Real.exp (momentPanelGrowth2620 : ℝ) -
    ((compactExp2620 momentScalarGrowth2620Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrowth2620Input 20).2 : ℝ) at h
  rw [momentScalarGrowth2620_replay] at h
  simpa only [momentPanelGrowth_owner2620] using h

theorem momentScalarGrowth2620_radius_le :
    (momentScalarGrowth2620Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrowth2620Expected]

end ConnesWeilRH.Dev
