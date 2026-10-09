import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P150 : ℚ := ((-29102100606433389632724329316272511025 : ℚ) / 685788833518670280374504460482772992)

def momentPanelGrowth2622K07P150 : ℚ := ((537931212774265758293628290129028228025 : ℚ) / 533100704086962518345964614393008226304)

theorem momentPanelPhase_owner2622K07P150 :
    (momentPanelPhase2622K07P150 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (121 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P150 :
    (momentPanelGrowth2622K07P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P150Input : RatPair2542 := (momentPanelPhase2622K07P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P150Expected : RatState2542 :=
  ((((397072422007169027544657825998413304754833977958733455931954112013234589006121 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1006741348010710153870800459839 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P150_replay :
    compactExp2620 momentScalarAmp2622K07P150Input 20 = momentScalarAmp2622K07P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K07P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P150_replay] at h
  simpa only [momentPanelPhase_owner2622K07P150] using h

theorem momentScalarAmp2622K07P150_radius_le :
    (momentScalarAmp2622K07P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P150Expected]

def momentScalarGrow2622K07P150Input : RatPair2542 := (momentPanelGrowth2622K07P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P150Expected : RatState2542 :=
  ((((1464766210878912471090700832481485942043320369715501645933981474496430461245310902348368461976705 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1856809979576412359541457266711440820905004595333 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P150_replay :
    compactExp2620 momentScalarGrow2622K07P150Input 20 = momentScalarGrow2622K07P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P150] using h

theorem momentScalarGrow2622K07P150_radius_le :
    (momentScalarGrow2622K07P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P150Expected]

end ConnesWeilRH.Dev
