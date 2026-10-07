import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P005 : ℚ := ((-1862476605491973059895229647829002949787532737896922987 : ℚ) / 17414705447321040084720782084834959856087721207398400)

def momentPanelGrowth2622P005 : ℚ := ((62340709823650155154949179927065409826319445442986397 : ℚ) / 9378730038309403570410208762446522440198304615628800)

theorem momentPanelPhase_owner2622P005 :
    (momentPanelPhase2622P005 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-169 / 200) 0 := by
  norm_num [momentPanelPhase2622P005, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P005 :
    (momentPanelGrowth2622P005 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P005, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P005Input : RatPair2542 := (momentPanelPhase2622P005 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P005Expected : RatState2542 :=
  ((((38143954771365127581511448998719497232060783419797 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819614629174706239 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P005_replay :
    compactExp2620 momentScalarAmp2622P005Input 20 = momentScalarAmp2622P005Expected := by
  decide +kernel

theorem momentScalarAmp2622P005_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-169 / 200) 0) -
      (momentScalarAmp2622P005Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P005]
  have h := compactExp_real_error2620 momentPanelPhase2622P005 20 hsmall
  change |Real.exp (momentPanelPhase2622P005 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P005Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P005_replay] at h
  simpa only [momentPanelPhase_owner2622P005] using h

theorem momentScalarAmp2622P005_radius_le :
    (momentScalarAmp2622P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P005Expected]

def momentScalarGrow2622P005Input : RatPair2542 := (momentPanelGrowth2622P005 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P005Expected : RatState2542 :=
  ((((1645763858388533270355352880063365917593042764449167811080774788511243866105736526292315991125820189 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((130390019874149834222821734043246908004946489058141 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622P005_replay :
    compactExp2620 momentScalarGrow2622P005Input 20 = momentScalarGrow2622P005Expected := by
  decide +kernel

theorem momentScalarGrow2622P005_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P005Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P005]
  have h := compactExp_real_error2620 momentPanelGrowth2622P005 20 hsmall
  change |Real.exp (momentPanelGrowth2622P005 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P005Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P005_replay] at h
  simpa only [momentPanelGrowth_owner2622P005] using h

theorem momentScalarGrow2622P005_radius_le :
    (momentScalarGrow2622P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [momentScalarGrow2622P005Expected]

end ConnesWeilRH.Dev
