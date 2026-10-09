import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P005 : ℚ := ((-73249331347349915053472447238322205446851019809204725 : ℚ) / 696588217892841603388831283393398394243508848295936)

def momentPanelGrowth2622K03P005 : ℚ := ((2485663345146815283280919188265754572124252793820675 : ℚ) / 375149201532376142816408350497860897607932184625152)

theorem momentPanelPhase_owner2622K03P005 :
    (momentPanelPhase2622K03P005 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-169 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P005, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P005 :
    (momentPanelGrowth2622K03P005 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P005, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P005Input : RatPair2542 := (momentPanelPhase2622K03P005 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P005Expected : RatState2542 :=
  ((((1792146353662801708541715671946800356778232692573 : ℚ) / 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096), 0), ((2417851639229258349413005 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P005_replay :
    compactExp2620 momentScalarAmp2622K03P005Input 20 = momentScalarAmp2622K03P005Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P005_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-169 / 200) 0) -
      (momentScalarAmp2622K03P005Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P005]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P005 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P005 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P005Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P005_replay] at h
  simpa only [momentPanelPhase_owner2622K03P005] using h

theorem momentScalarAmp2622K03P005_radius_le :
    (momentScalarAmp2622K03P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P005Expected]

def momentScalarGrow2622K03P005Input : RatPair2542 := (momentPanelGrowth2622K03P005 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P005Expected : RatState2542 :=
  ((((201398732203336819833760972215794078190176130670601260692679872300013741470933546565724254043418455 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((510603221087776805605663860873848655229726569509031 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P005_replay :
    compactExp2620 momentScalarGrow2622K03P005Input 20 = momentScalarGrow2622K03P005Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P005_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P005Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P005]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P005 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P005 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P005Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P005_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P005] using h

theorem momentScalarGrow2622K03P005_radius_le :
    (momentScalarGrow2622K03P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P005Expected]

end ConnesWeilRH.Dev
