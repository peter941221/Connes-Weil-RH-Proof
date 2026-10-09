import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P003 : ℚ := ((-820418221781541943062437724390762065809 : ℚ) / 6808804903945865761319092256715571200)

def momentPanelGrowth2622K20P003 : ℚ := ((53029911896792709546279510895168933466809 : ℚ) / 5993209663084304972814846585364860108800)

theorem momentPanelPhase_owner2622K20P003 :
    (momentPanelPhase2622K20P003 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-173 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P003, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P003 :
    (momentPanelGrowth2622K20P003 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P003, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P003Input : RatPair2542 := (momentPanelPhase2622K20P003 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P003Expected : RatState2542 :=
  ((((49981760026482084035002457955624554250751437 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K20P003_replay :
    compactExp2620 momentScalarAmp2622K20P003Input 20 = momentScalarAmp2622K20P003Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P003_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-173 / 200) 0) -
      (momentScalarAmp2622K20P003Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P003]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P003 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P003 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P003Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P003_replay] at h
  simpa only [momentPanelPhase_owner2622K20P003] using h

theorem momentScalarAmp2622K20P003_radius_le :
    (momentScalarAmp2622K20P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P003Expected]

def momentScalarGrow2622K20P003Input : RatPair2542 := (momentPanelGrowth2622K20P003 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P003Expected : RatState2542 :=
  ((((7436192086493781232230385159712106646093379177816647954309833398573371258570255838124136244319526921 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((9426413817411457943805451681746926642822623547571523 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K20P003_replay :
    compactExp2620 momentScalarGrow2622K20P003Input 20 = momentScalarGrow2622K20P003Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P003_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P003Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P003]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P003 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P003 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P003Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P003_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P003] using h

theorem momentScalarGrow2622K20P003_radius_le :
    (momentScalarGrow2622K20P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P003Expected]

end ConnesWeilRH.Dev
