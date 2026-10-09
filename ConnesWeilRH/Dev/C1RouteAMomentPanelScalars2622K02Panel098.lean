import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P098 : ℚ := ((-112866719900547155948615399997992852644877067042272309 : ℚ) / 3778495541669758189113706275520593424059683412377600)

def momentPanelGrowth2622K02P098 : ℚ := ((1344821767147698122770225027438342330317799839798971919 : ℚ) / 14042199218052417690129379708868688965492442006972006400)

theorem momentPanelPhase_owner2622K02P098 :
    (momentPanelPhase2622K02P098 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P098 :
    (momentPanelGrowth2622K02P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P098Input : RatPair2542 := (momentPanelPhase2622K02P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P098Expected : RatState2542 :=
  ((((227442147895392636626378094347211098994132738617545648029595353279603225741750578133 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((144162694357197782773189526941099727 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P098_replay :
    compactExp2620 momentScalarAmp2622K02P098Input 20 = momentScalarAmp2622K02P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K02P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P098_replay] at h
  simpa only [momentPanelPhase_owner2622K02P098] using h

theorem momentScalarAmp2622K02P098_radius_le :
    (momentScalarAmp2622K02P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P098Expected]

def momentScalarGrow2622K02P098Input : RatPair2542 := (momentPanelGrowth2622K02P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P098Expected : RatState2542 :=
  ((((2350666433178535165739328428616622121018508222102140000766264294109905918549695928666007878067073 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2979823442797663903733727806261471802327235357725 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P098_replay :
    compactExp2620 momentScalarGrow2622K02P098Input 20 = momentScalarGrow2622K02P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P098] using h

theorem momentScalarGrow2622K02P098_radius_le :
    (momentScalarGrow2622K02P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P098Expected]

end ConnesWeilRH.Dev
