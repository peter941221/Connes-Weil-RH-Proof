import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P051 : ℚ := ((-119282658092886454020445477141740965620683923945131031 : ℚ) / 3241850409212317273835790751007583252779770681753600)

def momentPanelGrowth2622K02P051 : ℚ := ((3759274219056062305230027592948256657519268563183903439 : ℚ) / 10260974778794205705723089990574508106731994783049318400)

theorem momentPanelPhase_owner2622K02P051 :
    (momentPanelPhase2622K02P051 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-77 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P051, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P051 :
    (momentPanelGrowth2622K02P051 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P051, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P051Input : RatPair2542 := (momentPanelPhase2622K02P051 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P051Expected : RatState2542 :=
  ((((111909672783554616383689528542724628465680618920707270299125068419211305456981117 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((283734686268267216300800712843965 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P051_replay :
    compactExp2620 momentScalarAmp2622K02P051Input 20 = momentScalarAmp2622K02P051Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P051_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-77 / 200) 0) -
      (momentScalarAmp2622K02P051Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P051]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P051 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P051 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P051Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P051_replay] at h
  simpa only [momentPanelPhase_owner2622K02P051] using h

theorem momentScalarAmp2622K02P051_radius_le :
    (momentScalarAmp2622K02P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P051Expected]

def momentScalarGrow2622K02P051Input : RatPair2542 := (momentPanelGrowth2622K02P051 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P051Expected : RatState2542 :=
  ((((770281442668420031056151218188051696848531265331937240067741891030414098933673454173890298617179 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((15256990499661652479670165052895213613708734235 : ℚ) / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896))

theorem momentScalarGrow2622K02P051_replay :
    compactExp2620 momentScalarGrow2622K02P051Input 20 = momentScalarGrow2622K02P051Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P051_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P051Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P051Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P051 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P051]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P051 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P051 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P051Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P051Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P051_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P051] using h

theorem momentScalarGrow2622K02P051_radius_le :
    (momentScalarGrow2622K02P051Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P051Expected]

end ConnesWeilRH.Dev
