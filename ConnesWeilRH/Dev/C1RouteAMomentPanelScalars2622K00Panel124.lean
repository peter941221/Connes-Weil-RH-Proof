import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P124 : ℚ := ((-5346303998655513520642022809165505568951331151487731739 : ℚ) / 160943300618449024795561405687778429155173146506035200)

def momentPanelGrowth2622K00P124 : ℚ := ((27845015289872939057070001615513381791757719418154557 : ℚ) / 93780449594169047096673007851811866825328408972492800)

theorem momentPanelPhase_owner2622K00P124 :
    (momentPanelPhase2622K00P124 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (69 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P124, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P124 :
    (momentPanelGrowth2622K00P124 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P124, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P124Input : RatPair2542 := (momentPanelPhase2622K00P124 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P124Expected : RatState2542 :=
  ((((3998832127839919085776450303082559878480672803259716907961995884374808278983346755 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5069282538999316191681772962895011 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P124_replay :
    compactExp2620 momentScalarAmp2622K00P124Input 20 = momentScalarAmp2622K00P124Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P124_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (69 / 200) 0) -
      (momentScalarAmp2622K00P124Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P124]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P124 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P124 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P124Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P124_replay] at h
  simpa only [momentPanelPhase_owner2622K00P124] using h

theorem momentScalarAmp2622K00P124_radius_le :
    (momentScalarAmp2622K00P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P124Expected]

def momentScalarGrow2622K00P124Input : RatPair2542 := (momentPanelGrowth2622K00P124 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P124Expected : RatState2542 :=
  ((((1437202808272553658187190005282273045034079594037366304107701146284748973126626728860083492302865 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((910935243335760014270209651550801863522410928315 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P124_replay :
    compactExp2620 momentScalarGrow2622K00P124Input 20 = momentScalarGrow2622K00P124Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P124_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P124Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P124]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P124 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P124 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P124Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P124_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P124] using h

theorem momentScalarGrow2622K00P124_radius_le :
    (momentScalarGrow2622K00P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P124Expected]

end ConnesWeilRH.Dev
