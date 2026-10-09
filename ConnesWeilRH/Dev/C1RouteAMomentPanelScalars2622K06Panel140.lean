import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P140 : ℚ := ((-18996767 : ℚ) / 496650)

def momentPanelGrowth2622K06P140 : ℚ := ((819745201 : ℚ) / 1368630025)

theorem momentPanelPhase_owner2622K06P140 :
    (momentPanelPhase2622K06P140 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P140 :
    (momentPanelGrowth2622K06P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P140Input : RatPair2542 := (momentPanelPhase2622K06P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P140Expected : RatState2542 :=
  ((((26114889573753819859615167267761126339295160494257359142499904262753329018237081 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((33105764257327148775989390224633 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P140_replay :
    compactExp2620 momentScalarAmp2622K06P140Input 20 = momentScalarAmp2622K06P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K06P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P140_replay] at h
  simpa only [momentPanelPhase_owner2622K06P140] using h

theorem momentScalarAmp2622K06P140_radius_le :
    (momentScalarAmp2622K06P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P140Expected]

def momentScalarGrow2622K06P140Input : RatPair2542 := (momentPanelGrowth2622K06P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P140Expected : RatState2542 :=
  ((((1943974861605453911060208800500443510432011714576863925414895668898988393728306549333281766266491 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4928558985061274143812882618654721352353901382037 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P140_replay :
    compactExp2620 momentScalarGrow2622K06P140Input 20 = momentScalarGrow2622K06P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P140] using h

theorem momentScalarGrow2622K06P140_radius_le :
    (momentScalarGrow2622K06P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P140Expected]

end ConnesWeilRH.Dev
