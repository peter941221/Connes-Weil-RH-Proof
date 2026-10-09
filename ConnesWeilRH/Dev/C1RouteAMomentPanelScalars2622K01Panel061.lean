import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P061 : ℚ := ((-85774043125667142885014759522346001803000348658894311 : ℚ) / 2622638997731836579438653383161919787860116058931200)

def momentPanelGrowth2622K01P061 : ℚ := ((208808773614400638083004191484693343498511807008674571 : ℚ) / 997732735455220890975525104146393448448939913327411200)

theorem momentPanelPhase_owner2622K01P061 :
    (momentPanelPhase2622K01P061 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-57 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P061, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P061 :
    (momentPanelGrowth2622K01P061 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P061, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P061Input : RatPair2542 := (momentPanelPhase2622K01P061 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P061Expected : RatState2542 :=
  ((((13362646458077187728525321253468364607537470653902665087587779751956569819484670869 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8469847574509214468877031413351925 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P061_replay :
    compactExp2620 momentScalarAmp2622K01P061Input 20 = momentScalarAmp2622K01P061Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P061_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-57 / 200) 0) -
      (momentScalarAmp2622K01P061Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P061]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P061 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P061 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P061Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P061_replay] at h
  simpa only [momentPanelPhase_owner2622K01P061] using h

theorem momentScalarAmp2622K01P061_radius_le :
    (momentScalarAmp2622K01P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P061Expected]

def momentScalarGrow2622K01P061Input : RatPair2542 := (momentPanelGrowth2622K01P061 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P061Expected : RatState2542 :=
  ((((1316616180197399085682712497793767376216984062407286923262514867073748644578225673782501408196683 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((834504478991549621788456323891794595265997265787 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P061_replay :
    compactExp2620 momentScalarGrow2622K01P061Input 20 = momentScalarGrow2622K01P061Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P061_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P061Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P061]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P061 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P061 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P061Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P061_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P061] using h

theorem momentScalarGrow2622K01P061_radius_le :
    (momentScalarGrow2622K01P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P061Expected]

end ConnesWeilRH.Dev
