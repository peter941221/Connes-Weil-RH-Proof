import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P174 : ℚ := ((-19355603 : ℚ) / 190650)

def momentPanelGrowth2622K06P174 : ℚ := ((684107 : ℚ) / 102675)

theorem momentPanelPhase_owner2622K06P174 :
    (momentPanelPhase2622K06P174 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (169 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P174, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P174 :
    (momentPanelGrowth2622K06P174 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P174, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P174Input : RatPair2542 := (momentPanelPhase2622K06P174 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P174Expected : RatState2542 :=
  ((((17304787326296345265420166638667003226655035282035989 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629174717363 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P174_replay :
    compactExp2620 momentScalarAmp2622K06P174Input 20 = momentScalarAmp2622K06P174Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P174_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (169 / 200) 0) -
      (momentScalarAmp2622K06P174Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P174]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P174 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P174 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P174Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P174_replay] at h
  simpa only [momentPanelPhase_owner2622K06P174] using h

theorem momentScalarAmp2622K06P174_radius_le :
    (momentScalarAmp2622K06P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P174Expected]

def momentScalarGrow2622K06P174Input : RatPair2542 := (momentPanelGrowth2622K06P174 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P174Expected : RatState2542 :=
  ((((1671986813624953314253671076236656777160014486157747698144086645807243879144551215095665375598572795 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1059740810129033002306949181307159969380994507352375 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P174_replay :
    compactExp2620 momentScalarGrow2622K06P174Input 20 = momentScalarGrow2622K06P174Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P174_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P174Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P174Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P174 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P174]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P174 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P174 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P174Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P174Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P174_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P174] using h

theorem momentScalarGrow2622K06P174_radius_le :
    (momentScalarGrow2622K06P174Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P174Expected]

end ConnesWeilRH.Dev
