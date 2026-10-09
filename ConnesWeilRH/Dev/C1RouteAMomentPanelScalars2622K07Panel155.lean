import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P155 : ℚ := ((-29185646908555606314065917043092484275 : ℚ) / 617639937250400667750041696161759232)

def momentPanelGrowth2622K07P155 : ℚ := ((106918275925667527023990684483895545075 : ℚ) / 80761350421023574664230970955212521472)

theorem momentPanelPhase_owner2622K07P155 :
    (momentPanelPhase2622K07P155 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P155 :
    (momentPanelGrowth2622K07P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P155Input : RatPair2542 := (momentPanelPhase2622K07P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P155Expected : RatState2542 :=
  ((((6421930839511682224178187878192287379594291380367021776697888839634455396071 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4071774601140938373687757803 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P155_replay :
    compactExp2620 momentScalarAmp2622K07P155Input 20 = momentScalarAmp2622K07P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K07P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P155_replay] at h
  simpa only [momentPanelPhase_owner2622K07P155] using h

theorem momentScalarAmp2622K07P155_radius_le :
    (momentScalarAmp2622K07P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P155Expected]

def momentScalarGrow2622K07P155Input : RatPair2542 := (momentPanelGrowth2622K07P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P155Expected : RatState2542 :=
  ((((4013488928303936971263272087103589577347154098037117827637431193954527071105835320225772877545417 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((317980951593876305734632568067216033472244650731 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K07P155_replay :
    compactExp2620 momentScalarGrow2622K07P155Input 20 = momentScalarGrow2622K07P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P155] using h

theorem momentScalarGrow2622K07P155_radius_le :
    (momentScalarGrow2622K07P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P155Expected]

end ConnesWeilRH.Dev
