import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P130 : ℚ := ((-57291441 : ℚ) / 1671950)

def momentPanelGrowth2622K06P130 : ℚ := ((228068587 : ℚ) / 576714675)

theorem momentPanelPhase_owner2622K06P130 :
    (momentPanelPhase2622K06P130 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (81 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P130, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P130 :
    (momentPanelGrowth2622K06P130 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P130, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P130Input : RatPair2542 := (momentPanelPhase2622K06P130 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P130Expected : RatState2542 :=
  ((((350646420492196431479537448861053629691316813366988824520224396098091279975472613 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3556093372741091215660355213641113 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P130_replay :
    compactExp2620 momentScalarAmp2622K06P130Input 20 = momentScalarAmp2622K06P130Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P130_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (81 / 200) 0) -
      (momentScalarAmp2622K06P130Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P130Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P130]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P130 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P130 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P130Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P130Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P130_replay] at h
  simpa only [momentPanelPhase_owner2622K06P130] using h

theorem momentScalarAmp2622K06P130_radius_le :
    (momentScalarAmp2622K06P130Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P130Expected]

def momentScalarGrow2622K06P130Input : RatPair2542 := (momentPanelGrowth2622K06P130 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P130Expected : RatState2542 :=
  ((((3172089720521297955564201631348398189504586124508672377200772378877664648484791164966363315364053 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2010549960835933803160345732235788831651625515717 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P130_replay :
    compactExp2620 momentScalarGrow2622K06P130Input 20 = momentScalarGrow2622K06P130Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P130_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P130Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P130Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P130 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P130]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P130 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P130 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P130Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P130Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P130_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P130] using h

theorem momentScalarGrow2622K06P130_radius_le :
    (momentScalarGrow2622K06P130Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P130Expected]

end ConnesWeilRH.Dev
