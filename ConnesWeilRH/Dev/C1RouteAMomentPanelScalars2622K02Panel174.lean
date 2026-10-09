import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P174 : ℚ := ((-110419612015232912112873524201853672892987448167785437 : ℚ) / 1088419090457565005295048880302184991005482575462400)

def momentPanelGrowth2622K02P174 : ℚ := ((3906079005452502132447977288398076140586341855407653 : ℚ) / 586170627394337723150638047652907652512394038476800)

theorem momentPanelPhase_owner2622K02P174 :
    (momentPanelPhase2622K02P174 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P174 :
    (momentPanelGrowth2622K02P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P174Input : RatPair2542 := (momentPanelPhase2622K02P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P174Expected : RatState2542 :=
  ((((18647680106608851668777663884659418296487567744154433 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349436445 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P174_replay :
    compactExp2620 momentScalarAmp2622K02P174Input 20 = momentScalarAmp2622K02P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K02P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P174_replay] at h
  simpa only [momentPanelPhase_owner2622K02P174] using h

theorem momentScalarAmp2622K02P174_radius_le :
    (momentScalarAmp2622K02P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P174Expected]

def momentScalarGrow2622K02P174Input : RatPair2542 := (momentPanelGrowth2622K02P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P174Expected : RatState2542 :=
  ((((836733153358220941180928938800233827197817204518905925051441295478901301368530207330276814208936229 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2121357086857049135944520112050666826374510226028795 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P174_replay :
    compactExp2620 momentScalarGrow2622K02P174Input 20 = momentScalarGrow2622K02P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P174] using h

theorem momentScalarGrow2622K02P174_radius_le :
    (momentScalarGrow2622K02P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P174Expected]

end ConnesWeilRH.Dev
