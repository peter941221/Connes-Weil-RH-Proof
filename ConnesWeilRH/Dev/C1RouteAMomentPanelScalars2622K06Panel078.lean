import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P078 : ℚ := ((-20302611 : ℚ) / 657850)

def momentPanelGrowth2622K06P078 : ℚ := ((1082581 : ℚ) / 9486400)

theorem momentPanelPhase_owner2622K06P078 :
    (momentPanelPhase2622K06P078 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-23 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P078, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P078 :
    (momentPanelGrowth2622K06P078 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P078, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P078Input : RatPair2542 := (momentPanelPhase2622K06P078 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P078Expected : RatState2542 :=
  ((((84405950788202785819170917908559207387691801244446431233537517658993192847762663145 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((53500201705035059718796921802674657 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P078_replay :
    compactExp2620 momentScalarAmp2622K06P078Input 20 = momentScalarAmp2622K06P078Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P078_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-23 / 200) 0) -
      (momentScalarAmp2622K06P078Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P078]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P078 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P078 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P078Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P078_replay] at h
  simpa only [momentPanelPhase_owner2622K06P078] using h

theorem momentScalarAmp2622K06P078_radius_le :
    (momentScalarAmp2622K06P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P078Expected]

def momentScalarGrow2622K06P078Input : RatPair2542 := (momentPanelGrowth2622K06P078 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P078Expected : RatState2542 :=
  ((((1197098768656110398989438523704205181463584700395312773634999095375063365799218844270763385470791 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3035005614931177439470646573249398026790464943199 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P078_replay :
    compactExp2620 momentScalarGrow2622K06P078Input 20 = momentScalarGrow2622K06P078Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P078_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P078Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P078]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P078 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P078 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P078Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P078_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P078] using h

theorem momentScalarGrow2622K06P078_radius_le :
    (momentScalarGrow2622K06P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P078Expected]

end ConnesWeilRH.Dev
