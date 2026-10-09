import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P015 : ℚ := ((-20884017 : ℚ) / 296650)

def momentPanelGrowth2622K06P015 : ℚ := ((2929 : ℚ) / 1225)

theorem momentPanelPhase_owner2622K06P015 :
    (momentPanelPhase2622K06P015 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-149 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P015, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P015 :
    (momentPanelGrowth2622K06P015 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P015, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P015Input : RatPair2542 := (momentPanelPhase2622K06P015 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P015Expected : RatState2542 :=
  ((((284738663537626573335519270330740627155842475085380757568185321603 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((302231545147000614526729 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P015_replay :
    compactExp2620 momentScalarAmp2622K06P015Input 20 = momentScalarAmp2622K06P015Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P015_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-149 / 200) 0) -
      (momentScalarAmp2622K06P015Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P015]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P015 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P015 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P015Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P015_replay] at h
  simpa only [momentPanelPhase_owner2622K06P015] using h

theorem momentScalarAmp2622K06P015_radius_le :
    (momentScalarAmp2622K06P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P015Expected]

def momentScalarGrow2622K06P015Input : RatPair2542 := (momentPanelGrowth2622K06P015 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P015Expected : RatState2542 :=
  ((((23334880537137313910849727660253517226842988896770456835489668983002832556171759534030365933109531 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29580407868213596882615940763308994306523151737409 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P015_replay :
    compactExp2620 momentScalarGrow2622K06P015Input 20 = momentScalarGrow2622K06P015Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P015_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P015Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P015Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P015 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P015]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P015 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P015 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P015Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P015Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P015_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P015] using h

theorem momentScalarGrow2622K06P015_radius_le :
    (momentScalarGrow2622K06P015Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P015Expected]

end ConnesWeilRH.Dev
