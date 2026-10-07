import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P155 : ℚ := ((-1771781279895340826332283551706625206013489832590482287 : ℚ) / 34770037390625512238389539473340820714501920155238400)

def momentPanelGrowth2622P155 : ℚ := ((5761888819704608038339276960332092120968873484957039791 : ℚ) / 4546459845775747763770310016931773290275638866241126400)

theorem momentPanelPhase_owner2622P155 :
    (momentPanelPhase2622P155 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (131 / 200) 0 := by
  norm_num [momentPanelPhase2622P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P155 :
    (momentPanelGrowth2622P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P155Input : RatPair2542 := (momentPanelPhase2622P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P155Expected : RatState2542 :=
  ((((79098580163875891090280904221588795016666206332781019095791545356227937639 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((202966322601141835795799833 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P155_replay :
    compactExp2620 momentScalarAmp2622P155Input 20 = momentScalarAmp2622P155Expected := by
  decide +kernel

theorem momentScalarAmp2622P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P155]
  have h := compactExp_real_error2620 momentPanelPhase2622P155 20 hsmall
  change |Real.exp (momentPanelPhase2622P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P155_replay] at h
  simpa only [momentPanelPhase_owner2622P155] using h

theorem momentScalarAmp2622P155_radius_le :
    (momentScalarAmp2622P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [momentScalarAmp2622P155Expected]

def momentScalarGrow2622P155Input : RatPair2542 := (momentPanelGrowth2622P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P155Expected : RatState2542 :=
  ((((7585693966187220294392678842373679970369469133774572944856610953605380707813068054432804242003847 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((600999867952604840250521656707061304970099651673 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622P155_replay :
    compactExp2620 momentScalarGrow2622P155Input 20 = momentScalarGrow2622P155Expected := by
  decide +kernel

theorem momentScalarGrow2622P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P155_replay] at h
  simpa only [momentPanelGrowth_owner2622P155] using h

theorem momentScalarGrow2622P155_radius_le :
    (momentScalarGrow2622P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P155Expected]

end ConnesWeilRH.Dev
