import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P086 : ℚ := ((-812630466257925500465838181526257175491 : ℚ) / 27010084869182929503570554537587507200)

def momentPanelGrowth2622K05P086 : ℚ := ((19635213378536469786072759456532123 : ℚ) / 514159083452569845247062820100505600)

theorem momentPanelPhase_owner2622K05P086 :
    (momentPanelPhase2622K05P086 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-7 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P086, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P086 :
    (momentPanelGrowth2622K05P086 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-7 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P086, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P086Input : RatPair2542 := (momentPanelPhase2622K05P086 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P086Expected : RatState2542 :=
  ((((183372237703090087494830557489596466525789967588256626210593910269248729190055180379 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((232458596896847316994709930465351653 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P086_replay :
    compactExp2620 momentScalarAmp2622K05P086Input 20 = momentScalarAmp2622K05P086Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P086_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-7 / 200) 0) -
      (momentScalarAmp2622K05P086Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P086]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P086 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P086 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P086Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P086_replay] at h
  simpa only [momentPanelPhase_owner2622K05P086] using h

theorem momentScalarAmp2622K05P086_radius_le :
    (momentScalarAmp2622K05P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P086Expected]

def momentScalarGrow2622K05P086Input : RatPair2542 := (momentPanelGrowth2622K05P086 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P086Expected : RatState2542 :=
  ((((1109567895175661426459494154815098373059723850422144476693661209405847566666850484187736984815821 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2813088714174518891883575752016383211779199055533 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P086_replay :
    compactExp2620 momentScalarGrow2622K05P086Input 20 = momentScalarGrow2622K05P086Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P086_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-7 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P086Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P086Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P086 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P086]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P086 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P086 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P086Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P086Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P086_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P086] using h

theorem momentScalarGrow2622K05P086_radius_le :
    (momentScalarGrow2622K05P086Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P086Expected]

end ConnesWeilRH.Dev
