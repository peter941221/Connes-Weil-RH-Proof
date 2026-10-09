import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P175 : ℚ := ((-91330181243152051514023311765256581825 : ℚ) / 872873779702753288364993906344984576)

def momentPanelGrowth2622K07P175 : ℚ := ((44069835899199550208941787183973097025 : ℚ) / 5730470314958121051559512694843244544)

theorem momentPanelPhase_owner2622K07P175 :
    (momentPanelPhase2622K07P175 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (171 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P175, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P175 :
    (momentPanelGrowth2622K07P175 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P175, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P175Input : RatPair2542 := (momentPanelPhase2622K07P175 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P175Expected : RatState2542 :=
  ((((193469083209136621247714861798737290400179168628533 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208925819614629174706713 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P175_replay :
    compactExp2620 momentScalarAmp2622K07P175Input 20 = momentScalarAmp2622K07P175Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P175_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (171 / 200) 0) -
      (momentScalarAmp2622K07P175Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P175]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P175 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P175 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P175Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P175_replay] at h
  simpa only [momentPanelPhase_owner2622K07P175] using h

theorem momentScalarAmp2622K07P175_radius_le :
    (momentScalarAmp2622K07P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P175Expected]

def momentScalarGrow2622K07P175Input : RatPair2542 := (momentPanelGrowth2622K07P175 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P175Expected : RatState2542 :=
  ((((4672121184556578607614601458277967229043183981916423210250745395492913094379346393427552348752647477 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((740321723323978822674587868534926645028923311948363 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P175_replay :
    compactExp2620 momentScalarGrow2622K07P175Input 20 = momentScalarGrow2622K07P175Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P175_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P175Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P175]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P175 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P175 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P175Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P175_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P175] using h

theorem momentScalarGrow2622K07P175_radius_le :
    (momentScalarGrow2622K07P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P175Expected]

end ConnesWeilRH.Dev
