import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P146 : ℚ := ((-108194616247549487455904656265885611915243511493272021 : ℚ) / 2591025461338399568073212348938613470589238221209600)

def momentPanelGrowth2622K02P146 : ℚ := ((5147133465066739154152970450578401188559678250519481679 : ℚ) / 6504824227001452024507232240191615978527519651817062400)

theorem momentPanelPhase_owner2622K02P146 :
    (momentPanelPhase2622K02P146 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P146 :
    (momentPanelGrowth2622K02P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P146Input : RatPair2542 := (momentPanelPhase2622K02P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P146Expected : RatState2542 :=
  ((((782597555835975979664788689238350242400592808910384261731054994068662405622515 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1984201955856881781718984379601 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P146_replay :
    compactExp2620 momentScalarAmp2622K02P146Input 20 = momentScalarAmp2622K02P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K02P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P146_replay] at h
  simpa only [momentPanelPhase_owner2622K02P146] using h

theorem momentScalarAmp2622K02P146_radius_le :
    (momentScalarAmp2622K02P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P146Expected]

def momentScalarGrow2622K02P146Input : RatPair2542 := (momentPanelGrowth2622K02P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P146Expected : RatState2542 :=
  ((((1178112873884538452813276689981858609048299230432022751418986149320552764843930673039151200293649 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5973737458944878299380491746716260188874393894389 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P146_replay :
    compactExp2620 momentScalarGrow2622K02P146Input 20 = momentScalarGrow2622K02P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P146] using h

theorem momentScalarGrow2622K02P146_radius_le :
    (momentScalarGrow2622K02P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P146Expected]

end ConnesWeilRH.Dev
