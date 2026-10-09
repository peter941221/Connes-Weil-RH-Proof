import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P080 : ℚ := ((-20251047 : ℚ) / 660650)

def momentPanelGrowth2622K06P080 : ℚ := ((8267 : ℚ) / 81675)

theorem momentPanelPhase_owner2622K06P080 :
    (momentPanelPhase2622K06P080 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P080 :
    (momentPanelGrowth2622K06P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P080Input : RatPair2542 := (momentPanelPhase2622K06P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P080Expected : RatState2542 :=
  ((((104010252323816910137348401136820040717426405525014055683771260911769414247550005295 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((16481564150389165271713524375744135 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K06P080_replay :
    compactExp2620 momentScalarAmp2622K06P080Input 20 = momentScalarAmp2622K06P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K06P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P080_replay] at h
  simpa only [momentPanelPhase_owner2622K06P080] using h

theorem momentScalarAmp2622K06P080_radius_le :
    (momentScalarAmp2622K06P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P080Expected]

def momentScalarGrow2622K06P080Input : RatPair2542 := (momentPanelGrowth2622K06P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P080Expected : RatState2542 :=
  ((((1181754163950003198049364542639699269044309940044817998192579378106996203889070040229360674179231 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1498051230647679136920433099301907804210489949021 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P080_replay :
    compactExp2620 momentScalarGrow2622K06P080Input 20 = momentScalarGrow2622K06P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P080] using h

theorem momentScalarGrow2622K06P080_radius_le :
    (momentScalarGrow2622K06P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P080Expected]

end ConnesWeilRH.Dev
