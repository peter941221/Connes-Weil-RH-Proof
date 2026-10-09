import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P058 : ℚ := ((-5606034152979892539153999142197104587773290932748335863 : ℚ) / 164560517170843009518115525648751229628821579549900800)

def momentPanelGrowth2622K00P058 : ℚ := ((62885469943948876893295674695571498192170143370783197 : ℚ) / 239565237917926613187490569915261098036007680134348800)

theorem momentPanelPhase_owner2622K00P058 :
    (momentPanelPhase2622K00P058 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-63 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P058, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P058 :
    (momentPanelGrowth2622K00P058 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P058, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P058Input : RatPair2542 := (momentPanelPhase2622K00P058 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P058Expected : RatState2542 :=
  ((((3424662481198650534198892041281123717846231761140440010693285163462408353029782843 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2170708248138276642012237841984685 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P058_replay :
    compactExp2620 momentScalarAmp2622K00P058Input 20 = momentScalarAmp2622K00P058Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P058_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-63 / 200) 0) -
      (momentScalarAmp2622K00P058Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P058]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P058 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P058 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P058Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P058_replay] at h
  simpa only [momentPanelPhase_owner2622K00P058] using h

theorem momentScalarAmp2622K00P058_radius_le :
    (momentScalarAmp2622K00P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P058Expected]

def momentScalarGrow2622K00P058Input : RatPair2542 := (momentPanelGrowth2622K00P058 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P058Expected : RatState2542 :=
  ((((2777155385348492106048157047559933090752889876248093238877912589743771505788656998985837449282279 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1760230904929481932065054181761396466524551661449 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P058_replay :
    compactExp2620 momentScalarGrow2622K00P058Input 20 = momentScalarGrow2622K00P058Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P058_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P058Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P058Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P058]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P058 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P058 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P058Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P058Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P058_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P058] using h

theorem momentScalarGrow2622K00P058_radius_le :
    (momentScalarGrow2622K00P058Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P058Expected]

end ConnesWeilRH.Dev
