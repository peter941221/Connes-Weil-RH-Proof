import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P098 : ℚ := ((-807761921602484634007967005133651379299 : ℚ) / 26847825592353716140178976527299379200)

def momentPanelGrowth2622K19P098 : ℚ := ((7021578593583045617009268864863649406009 : ℚ) / 99775826484833044745879104971697081548800)

theorem momentPanelPhase_owner2622K19P098 :
    (momentPanelPhase2622K19P098 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P098 :
    (momentPanelGrowth2622K19P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P098Input : RatPair2542 := (momentPanelPhase2622K19P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P098Expected : RatState2542 :=
  ((((91640989070543348631801599703682803140350176933463175193298288098325727532910484669 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((116172088067512868102481182714188051 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K19P098_replay :
    compactExp2620 momentScalarAmp2622K19P098Input 20 = momentScalarAmp2622K19P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K19P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P098_replay] at h
  simpa only [momentPanelPhase_owner2622K19P098] using h

theorem momentScalarAmp2622K19P098_radius_le :
    (momentScalarAmp2622K19P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P098Expected]

def momentScalarGrow2622K19P098Input : RatPair2542 := (momentPanelGrowth2622K19P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P098Expected : RatState2542 :=
  ((((2291719471066601164409466577173090571530182754140006491619583107757862038718114155020045309652569 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1452549684040536155056950212875974142377979162281 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K19P098_replay :
    compactExp2620 momentScalarGrow2622K19P098Input 20 = momentScalarGrow2622K19P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P098] using h

theorem momentScalarGrow2622K19P098_radius_le :
    (momentScalarGrow2622K19P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P098Expected]

end ConnesWeilRH.Dev
