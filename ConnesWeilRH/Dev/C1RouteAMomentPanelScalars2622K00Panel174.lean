import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P174 : ℚ := ((-1791277487835284235613982433961704599352298619543077013 : ℚ) / 17414705447321040084720782084834959856087721207398400)

def momentPanelGrowth2622K00P174 : ℚ := ((62340709823650155154949179927065409826319445442986397 : ℚ) / 9378730038309403570410208762446522440198304615628800)

theorem momentPanelPhase_owner2622K00P174 :
    (momentPanelPhase2622K00P174 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (169 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P174 :
    (momentPanelGrowth2622K00P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P174Input : RatPair2542 := (momentPanelPhase2622K00P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P174Expected : RatState2542 :=
  ((((1137590951678587800286941064782345804834556604455997 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258349418345 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P174_replay :
    compactExp2620 momentScalarAmp2622K00P174Input 20 = momentScalarAmp2622K00P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K00P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P174_replay] at h
  simpa only [momentPanelPhase_owner2622K00P174] using h

theorem momentScalarAmp2622K00P174_radius_le :
    (momentScalarAmp2622K00P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P174Expected]

def momentScalarGrow2622K00P174Input : RatPair2542 := (momentPanelGrowth2622K00P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P174Expected : RatState2542 :=
  ((((1645763858388533270355352880063365917593042764449167811080774788511243866105736526292315991125820189 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((130390019874149834222821734043246908004946489058141 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K00P174_replay :
    compactExp2620 momentScalarGrow2622K00P174Input 20 = momentScalarGrow2622K00P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P174] using h

theorem momentScalarGrow2622K00P174_radius_le :
    (momentScalarGrow2622K00P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622K00P174Expected]

end ConnesWeilRH.Dev
