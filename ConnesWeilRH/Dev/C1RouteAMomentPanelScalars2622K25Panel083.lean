import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K25
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K25P083 : ℚ := ((-814007375927058726264422399340833054769 : ℚ) / 26928955230768322821874765532443443200)

def momentPanelGrowth2622K25P083 : ℚ := ((1938206988072800339403709851584735210323 : ℚ) / 33473548283650779550665745328194034073600)

theorem momentPanelPhase_owner2622K25P083 :
    (momentPanelPhase2622K25P083 : ℝ) = momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K25P083 :
    (momentPanelGrowth2622K25P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K25P083Input : RatPair2542 := (momentPanelPhase2622K25P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K25P083Expected : RatState2542 :=
  ((((79566907794734828711297509506799728385019876463932553717099634542282075003148791579 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((100865946109659746314194113287698801 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K25P083_replay :
    compactExp2620 momentScalarAmp2622K25P083Input 20 = momentScalarAmp2622K25P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K25P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K25P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K25P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K25P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelPhase2622K25P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K25P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K25P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K25P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K25P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K25P083_replay] at h
  simpa only [momentPanelPhase_owner2622K25P083] using h

theorem momentScalarAmp2622K25P083_radius_le :
    (momentScalarAmp2622K25P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarAmp2622K25P083Expected]

def momentScalarGrow2622K25P083Input : RatPair2542 := (momentPanelGrowth2622K25P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K25P083Expected : RatState2542 :=
  ((((2263317136974390509901294860813865918725934139874732056604890227399204263164026378600919774470937 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1434547584380111232004108307035184926223174946833 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K25P083_replay :
    compactExp2620 momentScalarGrow2622K25P083Input 20 = momentScalarGrow2622K25P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K25P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 25).re * (storedWidth 25 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K25P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K25P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K25P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentPanelGrowth2622K25P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K25P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K25P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K25P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K25P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K25P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K25P083] using h

theorem momentScalarGrow2622K25P083_radius_le :
    (momentScalarGrow2622K25P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, momentScalarGrow2622K25P083Expected]

end ConnesWeilRH.Dev
