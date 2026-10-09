import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P006 : ℚ := ((-34659819396358310467817376737349737425 : ℚ) / 327520350279767174005900213766586368)

def momentPanelGrowth2622K07P006 : ℚ := ((126516852777788857167679620935913675 : ℚ) / 21458789360663467308536191860604928)

theorem momentPanelPhase_owner2622K07P006 :
    (momentPanelPhase2622K07P006 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-167 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P006, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P006 :
    (momentPanelGrowth2622K07P006 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P006, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P006Input : RatPair2542 := (momentPanelPhase2622K07P006 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P006Expected : RatState2542 :=
  ((((234646349614960250656028494872365184981991207079673 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412701 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P006_replay :
    compactExp2620 momentScalarAmp2622K07P006Input 20 = momentScalarAmp2622K07P006Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P006_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-167 / 200) 0) -
      (momentScalarAmp2622K07P006Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P006]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P006 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P006 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P006Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P006_replay] at h
  simpa only [momentPanelPhase_owner2622K07P006] using h

theorem momentScalarAmp2622K07P006_radius_le :
    (momentScalarAmp2622K07P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P006Expected]

def momentScalarGrow2622K07P006Input : RatPair2542 := (momentPanelGrowth2622K07P006 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P006Expected : RatState2542 :=
  ((((97056474174306065218364388857515816850590882775995877526914859769462987805319936280488948407870019 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((492132023864461090238708239213252331903089966728129 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P006_replay :
    compactExp2620 momentScalarGrow2622K07P006Input 20 = momentScalarGrow2622K07P006Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P006_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P006Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P006Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P006 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P006]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P006 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P006 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P006Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P006Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P006_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P006] using h

theorem momentScalarGrow2622K07P006_radius_le :
    (momentScalarGrow2622K07P006Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P006Expected]

end ConnesWeilRH.Dev
