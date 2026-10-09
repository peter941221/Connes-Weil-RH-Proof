import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P119 : ℚ := ((-19281793 : ℚ) / 608650)

def momentPanelGrowth2622K06P119 : ℚ := ((53281 : ℚ) / 207025)

theorem momentPanelPhase_owner2622K06P119 :
    (momentPanelPhase2622K06P119 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P119 :
    (momentPanelGrowth2622K06P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P119Input : RatPair2542 := (momentPanelPhase2622K06P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P119Expected : RatState2542 :=
  ((((18633308120949949545135155006678259762802122496172428682524529444930218606868295473 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((47242475719369524889185434666786185 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P119_replay :
    compactExp2620 momentScalarAmp2622K06P119Input 20 = momentScalarAmp2622K06P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K06P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P119_replay] at h
  simpa only [momentPanelPhase_owner2622K06P119] using h

theorem momentScalarAmp2622K06P119_radius_le :
    (momentScalarAmp2622K06P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P119Expected]

def momentScalarGrow2622K06P119Input : RatPair2542 := (momentPanelGrowth2622K06P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P119Expected : RatState2542 :=
  ((((43170875942824646232086726200806461395138959925227054437825811803960312313845980754097870625905 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((3502436695636490027625210890186597884056723109231 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P119_replay :
    compactExp2620 momentScalarGrow2622K06P119Input 20 = momentScalarGrow2622K06P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P119] using h

theorem momentScalarGrow2622K06P119_radius_le :
    (momentScalarGrow2622K06P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P119Expected]

end ConnesWeilRH.Dev
