import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P113 : ℚ := ((-802823268997170773243279704297241987749 : ℚ) / 25549751377720009233046352444994355200)

def momentPanelGrowth2622K05P113 : ℚ := ((62009156491150040091358265611301736969 : ℚ) / 351819691105422057757310218169797836800)

theorem momentPanelPhase_owner2622K05P113 :
    (momentPanelPhase2622K05P113 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (47 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P113, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P113 :
    (momentPanelGrowth2622K05P113 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P113, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P113Input : RatPair2542 := (momentPanelPhase2622K05P113 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P113Expected : RatState2542 :=
  ((((48218613637192261361432763322333636890649364459876991010270908965758726451139863013 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((15281546555241492137021232943613403 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P113_replay :
    compactExp2620 momentScalarAmp2622K05P113Input 20 = momentScalarAmp2622K05P113Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P113_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (47 / 200) 0) -
      (momentScalarAmp2622K05P113Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P113]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P113 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P113 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P113Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P113_replay] at h
  simpa only [momentPanelPhase_owner2622K05P113] using h

theorem momentScalarAmp2622K05P113_radius_le :
    (momentScalarAmp2622K05P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P113Expected]

def momentScalarGrow2622K05P113Input : RatPair2542 := (momentPanelGrowth2622K05P113 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P113Expected : RatState2542 :=
  ((((2547675849561913878918774092977318019560358917966947657553716765166286572237450837658927216233811 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3229562277034592657374303306004157894433726917679 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P113_replay :
    compactExp2620 momentScalarGrow2622K05P113Input 20 = momentScalarGrow2622K05P113Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P113_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P113Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P113]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P113 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P113 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P113Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P113_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P113] using h

theorem momentScalarGrow2622K05P113_radius_le :
    (momentScalarGrow2622K05P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P113Expected]

end ConnesWeilRH.Dev
