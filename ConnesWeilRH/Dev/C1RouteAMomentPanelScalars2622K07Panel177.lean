import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P177 : ℚ := ((-9811461499453507893878795394877067 : ℚ) / 81129638414606681695789005144064)

def momentPanelGrowth2622K07P177 : ℚ := ((2810535018822917303725938030487959025 : ℚ) / 268823056886799239798996868544856064)

theorem momentPanelPhase_owner2622K07P177 :
    (momentPanelPhase2622K07P177 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (7 / 8) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P177 :
    (momentPanelGrowth2622K07P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P177Input : RatPair2542 := (momentPanelPhase2622K07P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P177Expected : RatState2542 :=
  ((((32129566882321848786038702768096229481297243 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P177_replay :
    compactExp2620 momentScalarAmp2622K07P177Input 20 = momentScalarAmp2622K07P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K07P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P177_replay] at h
  simpa only [momentPanelPhase_owner2622K07P177] using h

theorem momentScalarAmp2622K07P177_radius_le :
    (momentScalarAmp2622K07P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P177Expected]

def momentScalarGrow2622K07P177Input : RatPair2542 := (momentPanelGrowth2622K07P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P177Expected : RatState2542 :=
  ((((9269177788145115895792689103583748609566600361645316000652319404635628111519340639652296641628121847 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((93999693053343094081062727873579258230457774287801205 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P177_replay :
    compactExp2620 momentScalarGrow2622K07P177Input 20 = momentScalarGrow2622K07P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P177] using h

theorem momentScalarGrow2622K07P177_radius_le :
    (momentScalarGrow2622K07P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P177Expected]

end ConnesWeilRH.Dev
