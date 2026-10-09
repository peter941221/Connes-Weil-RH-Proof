import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P035 : ℚ := ((-35797824177574445630467796970197666275 : ℚ) / 760428100860108427534630345215311872)

def momentPanelGrowth2622K07P035 : ℚ := ((798918313194174088251448801825891225 : ℚ) / 1052535363971899784980318658236514304)

theorem momentPanelPhase_owner2622K07P035 :
    (momentPanelPhase2622K07P035 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P035 :
    (momentPanelGrowth2622K07P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P035Input : RatPair2542 := (momentPanelPhase2622K07P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P035Expected : RatState2542 :=
  ((((7670125467954421234935968793649261906917517707042834062058590119135056371833 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4862946765573239214921808343 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P035_replay :
    compactExp2620 momentScalarAmp2622K07P035Input 20 = momentScalarAmp2622K07P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K07P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P035_replay] at h
  simpa only [momentPanelPhase_owner2622K07P035] using h

theorem momentScalarAmp2622K07P035_radius_le :
    (momentScalarAmp2622K07P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P035Expected]

def momentScalarGrow2622K07P035Input : RatPair2542 := (momentPanelGrowth2622K07P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P035Expected : RatState2542 :=
  ((((4562955862177510598026555677392005451384503182880955733346825993170844723927255988421764221888303 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((723028693802807187800591908033803964861907508321 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P035_replay :
    compactExp2620 momentScalarGrow2622K07P035Input 20 = momentScalarGrow2622K07P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P035] using h

theorem momentScalarGrow2622K07P035_radius_le :
    (momentScalarGrow2622K07P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P035Expected]

end ConnesWeilRH.Dev
