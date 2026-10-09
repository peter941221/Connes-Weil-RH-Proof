import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P139 : ℚ := ((-57010299 : ℚ) / 1509950)

def momentPanelGrowth2622K06P139 : ℚ := ((43 : ℚ) / 75)

theorem momentPanelPhase_owner2622K06P139 :
    (momentPanelPhase2622K06P139 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (99 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P139, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P139 :
    (momentPanelGrowth2622K06P139 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P139, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P139Input : RatPair2542 := (momentPanelPhase2622K06P139 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P139Expected : RatState2542 :=
  ((((42772622299032718662385714725311100426848799515287091901171218553117900550903859 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((54222693918510375860378691421745 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P139_replay :
    compactExp2620 momentScalarAmp2622K06P139Input 20 = momentScalarAmp2622K06P139Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P139_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (99 / 200) 0) -
      (momentScalarAmp2622K06P139Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P139]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P139 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P139 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P139Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P139_replay] at h
  simpa only [momentPanelPhase_owner2622K06P139] using h

theorem momentScalarAmp2622K06P139_radius_le :
    (momentScalarAmp2622K06P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P139Expected]

def momentScalarGrow2622K06P139Input : RatPair2542 := (momentPanelGrowth2622K06P139 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P139Expected : RatState2542 :=
  ((((29606300699563520262006653706344836900896296256459147265585691975515432389846748123689580449405 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((2401947157228833338390260955360568160877768279401 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P139_replay :
    compactExp2620 momentScalarGrow2622K06P139Input 20 = momentScalarGrow2622K06P139Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P139_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P139Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P139Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P139 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P139]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P139 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P139 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P139Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P139Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P139_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P139] using h

theorem momentScalarGrow2622K06P139_radius_le :
    (momentScalarGrow2622K06P139Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P139Expected]

end ConnesWeilRH.Dev
