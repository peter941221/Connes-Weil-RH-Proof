import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P076 : ℚ := ((-5539208100184980053024896465746420221282544655229141307 : ℚ) / 179358221248818401564927834580003595202837896547532800)

def momentPanelGrowth2622K00P076 : ℚ := ((510255166567470410630103332860178790128435043914293957 : ℚ) / 4572826248751720584229028368616995483627119174274252800)

theorem momentPanelPhase_owner2622K00P076 :
    (momentPanelPhase2622K00P076 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-27 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P076 :
    (momentPanelGrowth2622K00P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P076Input : RatPair2542 := (momentPanelPhase2622K00P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P076Expected : RatState2542 :=
  ((((41308429069702677954135801352860831769550094513224237158005655572189961507364004959 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((26183098606968883581438643354219301 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K00P076_replay :
    compactExp2620 momentScalarAmp2622K00P076Input 20 = momentScalarAmp2622K00P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K00P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P076_replay] at h
  simpa only [momentPanelPhase_owner2622K00P076] using h

theorem momentScalarAmp2622K00P076_radius_le :
    (momentScalarAmp2622K00P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P076Expected]

def momentScalarGrow2622K00P076Input : RatPair2542 := (momentPanelGrowth2622K00P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P076Expected : RatState2542 :=
  ((((149258486289237549170368464688835618578250900149260540428197067768968795577070979019490149102917 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((3027321433586953862751681843120734618067330451597 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P076_replay :
    compactExp2620 momentScalarGrow2622K00P076Input 20 = momentScalarGrow2622K00P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P076] using h

theorem momentScalarGrow2622K00P076_radius_le :
    (momentScalarGrow2622K00P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P076Expected]

end ConnesWeilRH.Dev
