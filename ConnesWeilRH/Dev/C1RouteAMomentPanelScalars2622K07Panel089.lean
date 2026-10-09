import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P089 : ℚ := ((-32495521490742536065705934835426097975 : ℚ) / 1081701468981950887049954805585805312)

def momentPanelGrowth2622K07P089 : ℚ := ((117259172775545679573585463549146402025 : ℚ) / 1351890221637002408425277738348753977344)

theorem momentPanelPhase_owner2622K07P089 :
    (momentPanelPhase2622K07P089 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-1 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P089, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P089 :
    (momentPanelGrowth2622K07P089 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P089, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P089Input : RatPair2542 := (momentPanelPhase2622K07P089 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P089Expected : RatState2542 :=
  ((((95912857739962918552559937653134254356928573969676842922730633576544328789313456419 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((121587475048377510873962185678694591 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P089_replay :
    compactExp2620 momentScalarAmp2622K07P089Input 20 = momentScalarAmp2622K07P089Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P089_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-1 / 200) 0) -
      (momentScalarAmp2622K07P089Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P089]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P089 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P089 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P089Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P089_replay] at h
  simpa only [momentPanelPhase_owner2622K07P089] using h

theorem momentScalarAmp2622K07P089_radius_le :
    (momentScalarAmp2622K07P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P089Expected]

def momentScalarGrow2622K07P089Input : RatPair2542 := (momentPanelGrowth2622K07P089 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P089Expected : RatState2542 :=
  ((((2329528885185708601831689592030205648125511089092964238256711460260576145164654475351405430678041 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1476514222641486603874509286282851431864504920909 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P089_replay :
    compactExp2620 momentScalarGrow2622K07P089Input 20 = momentScalarGrow2622K07P089Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P089_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P089Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P089]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P089 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P089 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P089Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P089_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P089] using h

theorem momentScalarGrow2622K07P089_radius_le :
    (momentScalarGrow2622K07P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P089Expected]

end ConnesWeilRH.Dev
