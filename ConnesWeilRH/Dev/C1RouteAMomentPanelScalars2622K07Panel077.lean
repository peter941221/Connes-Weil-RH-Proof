import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P077 : ℚ := ((-53642365238196718374851555082890335 : ℚ) / 1703722406706740315611569108025344)

def momentPanelGrowth2622K07P077 : ℚ := ((210977871072968672900723318766357036025 : ℚ) / 1306843801203676194480507851132563881984)

theorem momentPanelPhase_owner2622K07P077 :
    (momentPanelPhase2622K07P077 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P077 :
    (momentPanelGrowth2622K07P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P077Input : RatPair2542 := (momentPanelPhase2622K07P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P077Expected : RatState2542 :=
  ((((22627536412093423724446568266555069167759956018275549717837218256427712230215265237 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((28684671411882070795652237576313513 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P077_replay :
    compactExp2620 momentScalarAmp2622K07P077Input 20 = momentScalarAmp2622K07P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K07P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P077_replay] at h
  simpa only [momentPanelPhase_owner2622K07P077] using h

theorem momentScalarAmp2622K07P077_radius_le :
    (momentScalarAmp2622K07P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P077Expected]

def momentScalarGrow2622K07P077Input : RatPair2542 := (momentPanelGrowth2622K07P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P077Expected : RatState2542 :=
  ((((2510218052635010272224874676387060736596647193438774398532917576618710131183282947608529739663247 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1591039465603748838298506726750637919728797566789 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P077_replay :
    compactExp2620 momentScalarGrow2622K07P077Input 20 = momentScalarGrow2622K07P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P077] using h

theorem momentScalarGrow2622K07P077_radius_le :
    (momentScalarGrow2622K07P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P077Expected]

end ConnesWeilRH.Dev
