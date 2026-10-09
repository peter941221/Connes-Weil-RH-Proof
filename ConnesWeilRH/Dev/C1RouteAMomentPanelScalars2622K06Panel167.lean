import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P167 : ℚ := ((-153397 : ℚ) / 2130)

def momentPanelGrowth2622K06P167 : ℚ := ((74083441 : ℚ) / 23961025)

theorem momentPanelPhase_owner2622K06P167 :
    (momentPanelPhase2622K06P167 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (31 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P167, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P167 :
    (momentPanelGrowth2622K06P167 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P167, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P167Input : RatPair2542 := (momentPanelPhase2622K06P167 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P167Expected : RatState2542 :=
  ((((112941053090691063404823612443512634847154094613199296978797417935 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231472801110825152081 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P167_replay :
    compactExp2620 momentScalarAmp2622K06P167Input 20 = momentScalarAmp2622K06P167Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P167_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (31 / 40) 0) -
      (momentScalarAmp2622K06P167Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P167]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P167 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P167 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P167Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P167_replay] at h
  simpa only [momentPanelPhase_owner2622K06P167] using h

theorem momentScalarAmp2622K06P167_radius_le :
    (momentScalarAmp2622K06P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P167Expected]

def momentScalarGrow2622K06P167Input : RatPair2542 := (momentPanelGrowth2622K06P167 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P167Expected : RatState2542 :=
  ((((23514393373897723510400738739374423778702213287945457603059780526618265100958251872948386330012999 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((59615893965172562150092408154560021647965234942223 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P167_replay :
    compactExp2620 momentScalarGrow2622K06P167Input 20 = momentScalarGrow2622K06P167Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P167_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P167Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P167]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P167 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P167 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P167Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P167_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P167] using h

theorem momentScalarGrow2622K06P167_radius_le :
    (momentScalarGrow2622K06P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P167Expected]

end ConnesWeilRH.Dev
