import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P169 : ℚ := ((-57659679 : ℚ) / 735950)

def momentPanelGrowth2622K06P169 : ℚ := ((2527 : ℚ) / 675)

theorem momentPanelPhase_owner2622K06P169 :
    (momentPanelPhase2622K06P169 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (159 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P169, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P169 :
    (momentPanelGrowth2622K06P169 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P169, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P169Input : RatPair2542 := (momentPanelPhase2622K06P169 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P169Expected : RatState2542 :=
  ((((201283534046455517491713094998305933065297732507449308898625705 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819742217327298807 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P169_replay :
    compactExp2620 momentScalarAmp2622K06P169Input 20 = momentScalarAmp2622K06P169Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P169_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (159 / 200) 0) -
      (momentScalarAmp2622K06P169Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P169Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P169 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P169]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P169 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P169 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P169Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P169Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P169_replay] at h
  simpa only [momentPanelPhase_owner2622K06P169] using h

theorem momentScalarAmp2622K06P169_radius_le :
    (momentScalarAmp2622K06P169Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P169Expected]

def momentScalarGrow2622K06P169Input : RatPair2542 := (momentPanelGrowth2622K06P169 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P169Expected : RatState2542 :=
  ((((90254418589757931214042116754966329874743053637058389550179397772793793224458376611458572062737547 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57205329710208303897893570035696208778475826429599 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P169_replay :
    compactExp2620 momentScalarGrow2622K06P169Input 20 = momentScalarGrow2622K06P169Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P169_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P169Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P169Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P169 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P169]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P169 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P169 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P169Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P169Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P169_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P169] using h

theorem momentScalarGrow2622K06P169_radius_le :
    (momentScalarGrow2622K06P169Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P169Expected]

end ConnesWeilRH.Dev
