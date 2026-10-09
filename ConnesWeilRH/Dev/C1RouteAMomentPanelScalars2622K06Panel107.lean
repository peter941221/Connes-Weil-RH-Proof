import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P107 : ℚ := ((-156381 : ℚ) / 5170)

def momentPanelGrowth2622K06P107 : ℚ := ((22726561 : ℚ) / 146289025)

theorem momentPanelPhase_owner2622K06P107 :
    (momentPanelPhase2622K06P107 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (7 / 40) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P107, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P107 :
    (momentPanelGrowth2622K06P107 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P107, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P107Input : RatPair2542 := (momentPanelPhase2622K06P107 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P107Expected : RatState2542 :=
  ((((19501435463209238773022055882432275736809623252865491185306090806465280741219221583 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((49443438992016965815508705927072385 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K06P107_replay :
    compactExp2620 momentScalarAmp2622K06P107Input 20 = momentScalarAmp2622K06P107Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P107_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (7 / 40) 0) -
      (momentScalarAmp2622K06P107Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P107]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P107 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P107 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P107Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P107_replay] at h
  simpa only [momentPanelPhase_owner2622K06P107] using h

theorem momentScalarAmp2622K06P107_radius_le :
    (momentScalarAmp2622K06P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P107Expected]

def momentScalarGrow2622K06P107Input : RatPair2542 := (momentPanelGrowth2622K06P107 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P107Expected : RatState2542 :=
  ((((311873115405595001803933221896482399421357576498024653741481555624697797661124758708449399931711 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3162768666925370868631056654907143252820705151355 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P107_replay :
    compactExp2620 momentScalarGrow2622K06P107Input 20 = momentScalarGrow2622K06P107Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P107_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P107Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P107Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P107 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P107]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P107 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P107 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P107Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P107Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P107_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P107] using h

theorem momentScalarGrow2622K06P107_radius_le :
    (momentScalarGrow2622K06P107Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P107Expected]

end ConnesWeilRH.Dev
