import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P070 : ℚ := ((-5563535904510395998021371579758014759114860321887096751 : ℚ) / 175741004696424416842373714619030794729189463503667200)

def momentPanelGrowth2622K00P070 : ℚ := ((1057764093614549345889751986291896104462965629413 : ℚ) / 6850788924988607429079772653357576654637183795200)

theorem momentPanelPhase_owner2622K00P070 :
    (momentPanelPhase2622K00P070 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-39 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P070 :
    (momentPanelGrowth2622K00P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P070Input : RatPair2542 := (momentPanelPhase2622K00P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P070Expected : RatState2542 :=
  ((((38096393496353696761368398133824774400452206947931855046775228416328093523792270415 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((12073593529828056555535234780049611 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K00P070_replay :
    compactExp2620 momentScalarAmp2622K00P070Input 20 = momentScalarAmp2622K00P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K00P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P070_replay] at h
  simpa only [momentPanelPhase_owner2622K00P070] using h

theorem momentScalarAmp2622K00P070_radius_le :
    (momentScalarAmp2622K00P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P070Expected]

def momentScalarGrow2622K00P070Input : RatPair2542 := (momentPanelGrowth2622K00P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P070Expected : RatState2542 :=
  ((((2492607085667527187598616508261817394991630468223884496647228469326181446918446043375305346345507 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3159754403013189633686739702875121929992104918187 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P070_replay :
    compactExp2620 momentScalarGrow2622K00P070Input 20 = momentScalarGrow2622K00P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P070] using h

theorem momentScalarGrow2622K00P070_radius_le :
    (momentScalarGrow2622K00P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P070Expected]

end ConnesWeilRH.Dev
