import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P001 : ℚ := ((-2455853614624782758251383150246703741263 : ℚ) / 17586877367326363424604661590104473600)

def momentPanelGrowth2622K05P001 : ℚ := ((18071963463998869015549097204091058553483 : ℚ) / 1461091039461616660414536522428684697600)

theorem momentPanelPhase_owner2622K05P001 :
    (momentPanelPhase2622K05P001 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-177 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P001, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P001 :
    (momentPanelGrowth2622K05P001 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P001, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P001Input : RatPair2542 := (momentPanelPhase2622K05P001 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P001Expected : RatState2542 :=
  ((((120812657285568251933430836057386583 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P001_replay :
    compactExp2620 momentScalarAmp2622K05P001Input 20 = momentScalarAmp2622K05P001Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P001_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-177 / 200) 0) -
      (momentScalarAmp2622K05P001Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P001]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P001 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P001 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P001Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P001_replay] at h
  simpa only [momentPanelPhase_owner2622K05P001] using h

theorem momentScalarAmp2622K05P001_radius_le :
    (momentScalarAmp2622K05P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P001Expected]

def momentScalarGrow2622K05P001Input : RatPair2542 := (momentPanelGrowth2622K05P001 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P001Expected : RatState2542 :=
  ((((251348519921163626870390041541583570785524509070511307584310591121855172225603080678484951022497304817 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((318618343757633405397042742097903764878768064129559233 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P001_replay :
    compactExp2620 momentScalarGrow2622K05P001Input 20 = momentScalarGrow2622K05P001Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P001_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P001Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P001Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P001 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P001]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P001 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P001 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P001Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P001Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P001_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P001] using h

theorem momentScalarGrow2622K05P001_radius_le :
    (momentScalarGrow2622K05P001Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P001Expected]

end ConnesWeilRH.Dev
