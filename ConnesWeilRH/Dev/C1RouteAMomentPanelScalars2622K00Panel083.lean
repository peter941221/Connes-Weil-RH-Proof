import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P083 : ℚ := ((-1836412347810795803839882314962977896488136778493891071 : ℚ) / 60638616371382493890594761012419030162411926165913600)

def momentPanelGrowth2622K00P083 : ℚ := ((5020524486704959660564064677395102850491064232537648957 : ℚ) / 75375729788508978363768478741067550209302413697666252800)

theorem momentPanelPhase_owner2622K00P083 :
    (momentPanelPhase2622K00P083 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-13 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P083 :
    (momentPanelGrowth2622K00P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P083Input : RatPair2542 := (momentPanelPhase2622K00P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P083Expected : RatState2542 :=
  ((((37595151575762462069741268406219223923218701459249819733604412386138692803331914793 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((190635571622924941374064325422205809 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P083_replay :
    compactExp2620 momentScalarAmp2622K00P083Input 20 = momentScalarAmp2622K00P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K00P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P083_replay] at h
  simpa only [momentPanelPhase_owner2622K00P083] using h

theorem momentScalarAmp2622K00P083_radius_le :
    (momentScalarAmp2622K00P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P083Expected]

def momentScalarGrow2622K00P083Input : RatPair2542 := (momentPanelGrowth2622K00P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P083Expected : RatState2542 :=
  ((((1141551516319190770875905202775295428529313808229169468417020371794566027221885139487863567183661 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2894176745865792939054692801725991839751754957383 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P083_replay :
    compactExp2620 momentScalarGrow2622K00P083Input 20 = momentScalarGrow2622K00P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P083] using h

theorem momentScalarGrow2622K00P083_radius_le :
    (momentScalarGrow2622K00P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P083Expected]

end ConnesWeilRH.Dev
