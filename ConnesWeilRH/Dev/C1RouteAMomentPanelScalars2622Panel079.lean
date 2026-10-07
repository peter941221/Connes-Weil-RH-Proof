import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P079 : ℚ := ((-5526525118239543228442503800304754120496678040065322069 : ℚ) / 180673572722416214191311150929448249920528235836211200)

def momentPanelGrowth2622P079 : ℚ := ((6821109446289372122293649517056027669821324371577170637 : ℚ) / 74288920633448785681219263607338904248810770860395724800)

theorem momentPanelPhase_owner2622P079 :
    (momentPanelPhase2622P079 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-21 / 200) 0 := by
  norm_num [momentPanelPhase2622P079, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P079 :
    (momentPanelGrowth2622P079 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P079, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P079Input : RatPair2542 := (momentPanelPhase2622P079 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P079Expected : RatState2542 :=
  ((((110969132479360204402495108009324741813158988878596925193226492007647012807204257725 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((70337095501522022774414116351457787 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P079_replay :
    compactExp2620 momentScalarAmp2622P079Input 20 = momentScalarAmp2622P079Expected := by
  decide +kernel

theorem momentScalarAmp2622P079_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-21 / 200) 0) -
      (momentScalarAmp2622P079Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P079]
  have h := compactExp_real_error2620 momentPanelPhase2622P079 20 hsmall
  change |Real.exp (momentPanelPhase2622P079 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P079Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P079_replay] at h
  simpa only [momentPanelPhase_owner2622P079] using h

theorem momentScalarAmp2622P079_radius_le :
    (momentScalarAmp2622P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P079Expected]

def momentScalarGrow2622P079Input : RatPair2542 := (momentPanelGrowth2622P079 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P079Expected : RatState2542 :=
  ((((2341396428760851152433883799689085261305148722517788172377289321299459956606756255747668855998775 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((742018082097839799631269939456756483222890768563 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622P079_replay :
    compactExp2620 momentScalarGrow2622P079Input 20 = momentScalarGrow2622P079Expected := by
  decide +kernel

theorem momentScalarGrow2622P079_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P079Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P079]
  have h := compactExp_real_error2620 momentPanelGrowth2622P079 20 hsmall
  change |Real.exp (momentPanelGrowth2622P079 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P079Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P079_replay] at h
  simpa only [momentPanelGrowth_owner2622P079] using h

theorem momentScalarGrow2622P079_radius_le :
    (momentScalarGrow2622P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P079Expected]

end ConnesWeilRH.Dev
