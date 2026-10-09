import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K23
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K23P088 : ℚ := ((-2435773532117002672965272203989244415037 : ℚ) / 81111384245963395192407452617906585600)

def momentPanelGrowth2622K23P088 : ℚ := ((58049126904026844160554819817806590123 : ℚ) / 2111061137620238090820350137140353433600)

theorem momentPanelPhase_owner2622K23P088 :
    (momentPanelPhase2622K23P088 : ℝ) = momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-3 / 200) 0 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P088, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K23P088 :
    (momentPanelGrowth2622K23P088 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2))
      (-3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P088, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K23P088Input : RatPair2542 := (momentPanelPhase2622K23P088 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K23P088Expected : RatState2542 :=
  ((((12123345881019331755183751706784410879078499347414165484653242715038392748924710087 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((30737213631046023383993284574036361 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K23P088_replay :
    compactExp2620 momentScalarAmp2622K23P088Input 20 = momentScalarAmp2622K23P088Expected := by
  decide +kernel

theorem momentScalarAmp2622K23P088_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-3 / 200) 0) -
      (momentScalarAmp2622K23P088Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K23P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K23P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P088]
  have h := compactExp_real_error2620 momentPanelPhase2622K23P088 20 hsmall
  change |Real.exp (momentPanelPhase2622K23P088 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K23P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K23P088Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K23P088_replay] at h
  simpa only [momentPanelPhase_owner2622K23P088] using h

theorem momentScalarAmp2622K23P088_radius_le :
    (momentScalarAmp2622K23P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarAmp2622K23P088Expected]

def momentScalarGrow2622K23P088Input : RatPair2542 := (momentPanelGrowth2622K23P088 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K23P088Expected : RatState2542 :=
  ((((2195536547689569656073945817892086333540003712027661590662103606494063074877322906661282861818137 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1391586574758215454862030521612244424391801233233 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K23P088_replay :
    compactExp2620 momentScalarGrow2622K23P088Input 20 = momentScalarGrow2622K23P088Expected := by
  decide +kernel

theorem momentScalarGrow2622K23P088_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K23P088Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K23P088Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K23P088 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P088]
  have h := compactExp_real_error2620 momentPanelGrowth2622K23P088 20 hsmall
  change |Real.exp (momentPanelGrowth2622K23P088 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K23P088Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K23P088Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K23P088_replay] at h
  simpa only [momentPanelGrowth_owner2622K23P088] using h

theorem momentScalarGrow2622K23P088_radius_le :
    (momentScalarGrow2622K23P088Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarGrow2622K23P088Expected]

end ConnesWeilRH.Dev
