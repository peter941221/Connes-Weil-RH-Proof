import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K14
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K14P099 : ℚ := ((-807353264733996922486380463759805208657 : ℚ) / 26799147809304952131161503124212940800)

def momentPanelGrowth2622K14P099 : ℚ := ((254137878392937395338835671763820523 : ℚ) / 3313131608756500363751783497570713600)

theorem momentPanelPhase_owner2622K14P099 :
    (momentPanelPhase2622K14P099 : ℝ) = momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (19 / 200) 0 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P099, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K14P099 :
    (momentPanelGrowth2622K14P099 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2))
      (19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P099, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K14P099Input : RatPair2542 := (momentPanelPhase2622K14P099 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K14P099Expected : RatState2542 :=
  ((((44050253764733103858249623534663513505924466861999162657479258070174824729267934519 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((223367739870330928547707199561245157 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K14P099_replay :
    compactExp2620 momentScalarAmp2622K14P099Input 20 = momentScalarAmp2622K14P099Expected := by
  decide +kernel

theorem momentScalarAmp2622K14P099_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (19 / 200) 0) -
      (momentScalarAmp2622K14P099Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K14P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K14P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P099]
  have h := compactExp_real_error2620 momentPanelPhase2622K14P099 20 hsmall
  change |Real.exp (momentPanelPhase2622K14P099 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K14P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K14P099Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K14P099_replay] at h
  simpa only [momentPanelPhase_owner2622K14P099] using h

theorem momentScalarAmp2622K14P099_radius_le :
    (momentScalarAmp2622K14P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarAmp2622K14P099Expected]

def momentScalarGrow2622K14P099Input : RatPair2542 := (momentPanelGrowth2622K14P099 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K14P099Expected : RatState2542 :=
  ((((288284786074839955653014131610935815675440332897336203943616606618345210783842353446217368209109 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((730888710742336618779380198713860601194506550731 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K14P099_replay :
    compactExp2620 momentScalarGrow2622K14P099Input 20 = momentScalarGrow2622K14P099Expected := by
  decide +kernel

theorem momentScalarGrow2622K14P099_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K14P099Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K14P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K14P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P099]
  have h := compactExp_real_error2620 momentPanelGrowth2622K14P099 20 hsmall
  change |Real.exp (momentPanelGrowth2622K14P099 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K14P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K14P099Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K14P099_replay] at h
  simpa only [momentPanelGrowth_owner2622K14P099] using h

theorem momentScalarGrow2622K14P099_radius_le :
    (momentScalarGrow2622K14P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarGrow2622K14P099Expected]

end ConnesWeilRH.Dev
