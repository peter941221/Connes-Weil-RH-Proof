import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P096 : ℚ := ((-1817341745516461491669329766827729652651694578946108929 : ℚ) / 60638616371382493890594761012419030162411926165913600)

def momentPanelGrowth2622K00P096 : ℚ := ((5020524486704959660564064677395102850491064232537648957 : ℚ) / 75375729788508978363768478741067550209302413697666252800)

theorem momentPanelPhase_owner2622K00P096 :
    (momentPanelPhase2622K00P096 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (13 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P096, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P096 :
    (momentPanelGrowth2622K00P096 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P096, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P096Input : RatPair2542 := (momentPanelPhase2622K00P096 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P096Expected : RatState2542 :=
  ((((102978298843173939606995706297340926067865644451545860865303031080317592599450017419 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((261088466914901536498403666315430361 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P096_replay :
    compactExp2620 momentScalarAmp2622K00P096Input 20 = momentScalarAmp2622K00P096Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P096_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (13 / 200) 0) -
      (momentScalarAmp2622K00P096Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P096]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P096 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P096 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P096Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P096_replay] at h
  simpa only [momentPanelPhase_owner2622K00P096] using h

theorem momentScalarAmp2622K00P096_radius_le :
    (momentScalarAmp2622K00P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [momentScalarAmp2622K00P096Expected]

def momentScalarGrow2622K00P096Input : RatPair2542 := (momentPanelGrowth2622K00P096 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P096Expected : RatState2542 :=
  ((((1141551516319190770875905202775295428529313808229169468417020371794566027221885139487863567183661 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2894176745865792939054692801725991839751754957383 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P096_replay :
    compactExp2620 momentScalarGrow2622K00P096Input 20 = momentScalarGrow2622K00P096Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P096_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P096Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P096Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P096 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P096]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P096 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P096 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P096Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P096Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P096_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P096] using h

theorem momentScalarGrow2622K00P096_radius_le :
    (momentScalarGrow2622K00P096Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P096Expected]

end ConnesWeilRH.Dev
