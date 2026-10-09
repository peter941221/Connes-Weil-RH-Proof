import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P122 : ℚ := ((-14272443604822267605424904158280047477948836268643329 : ℚ) / 435710175629275432489473540753541875234924889374720)

def momentPanelGrowth2622K00P122 : ℚ := ((49601968103313952605266845638706837530692452574039504791 : ℚ) / 181331068055106762471173843336824038863188166701377126400)

theorem momentPanelPhase_owner2622K00P122 :
    (momentPanelPhase2622K00P122 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (13 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P122 :
    (momentPanelGrowth2622K00P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P122Input : RatPair2542 := (momentPanelPhase2622K00P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P122Expected : RatState2542 :=
  ((((6345977368557538093471697818351322066901835498080377195365376530775243678675164351 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4022366664537982523109560623465657 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K00P122_replay :
    compactExp2620 momentScalarAmp2622K00P122Input 20 = momentScalarAmp2622K00P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K00P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P122_replay] at h
  simpa only [momentPanelPhase_owner2622K00P122] using h

theorem momentScalarAmp2622K00P122_radius_le :
    (momentScalarAmp2622K00P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P122Expected]

def momentScalarGrow2622K00P122Input : RatPair2542 := (momentPanelGrowth2622K00P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P122Expected : RatState2542 :=
  ((((702000033743545986088985565761732744109763859426529241697682000274878565397453871321480769683175 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1779781063976120165312426165429766493070931235847 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K00P122_replay :
    compactExp2620 momentScalarGrow2622K00P122Input 20 = momentScalarGrow2622K00P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P122] using h

theorem momentScalarGrow2622K00P122_radius_le :
    (momentScalarGrow2622K00P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P122Expected]

end ConnesWeilRH.Dev
