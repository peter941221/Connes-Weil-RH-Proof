import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P100 : ℚ := ((-5434737161742228658085132445067368526922816032254677931 : ℚ) / 180673572722416214191311150929448249920528235836211200)

def momentPanelGrowth2622K00P100 : ℚ := ((6821109446289372122293649517056027669821324371577170637 : ℚ) / 74288920633448785681219263607338904248810770860395724800)

theorem momentPanelPhase_owner2622K00P100 :
    (momentPanelPhase2622K00P100 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (21 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P100 :
    (momentPanelGrowth2622K00P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P100Input : RatPair2542 := (momentPanelPhase2622K00P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P100Expected : RatState2542 :=
  ((((184432598484494877567577217861093079257492203265871449626167286085690937011458865919 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((116901400580091031576753099812265841 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P100_replay :
    compactExp2620 momentScalarAmp2622K00P100Input 20 = momentScalarAmp2622K00P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K00P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P100_replay] at h
  simpa only [momentPanelPhase_owner2622K00P100] using h

theorem momentScalarAmp2622K00P100_radius_le :
    (momentScalarAmp2622K00P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P100Expected]

def momentScalarGrow2622K00P100Input : RatPair2542 := (momentPanelGrowth2622K00P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P100Expected : RatState2542 :=
  ((((2341396428760851152433883799689085261305148722517788172377289321299459956606756255747668855998775 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((742018082097839799631269939456756483222890768563 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P100_replay :
    compactExp2620 momentScalarGrow2622K00P100Input 20 = momentScalarGrow2622K00P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P100] using h

theorem momentScalarGrow2622K00P100_radius_le :
    (momentScalarGrow2622K00P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P100Expected]

end ConnesWeilRH.Dev
