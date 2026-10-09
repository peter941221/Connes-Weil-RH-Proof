import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P004 : ℚ := ((-85757099414904254071206434620603095823406893891586397 : ℚ) / 767787896291171118015304937265355908617098546380800)

def momentPanelGrowth2622K01P004 : ℚ := ((38366667695359617093814117490199937450746473526937891 : ℚ) / 5040574995137320862936522101155545735784536683315200)

theorem momentPanelPhase_owner2622K01P004 :
    (momentPanelPhase2622K01P004 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P004 :
    (momentPanelGrowth2622K01P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P004Input : RatPair2542 := (momentPanelPhase2622K01P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P004Expected : RatState2542 :=
  ((((331585051572897764237453575422544608454578428331 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((604462909807314587353089 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P004_replay :
    compactExp2620 momentScalarAmp2622K01P004Input 20 = momentScalarAmp2622K01P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K01P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P004_replay] at h
  simpa only [momentPanelPhase_owner2622K01P004] using h

theorem momentScalarAmp2622K01P004_radius_le :
    (momentScalarAmp2622K01P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P004Expected]

def momentScalarGrow2622K01P004Input : RatPair2542 := (momentPanelGrowth2622K01P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P004Expected : RatState2542 :=
  ((((4317770856608991889874873875500200192104822363633143359920693354717140307257841768740954632172559231 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5473385086829702080077366155986534741939963147686631 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P004_replay :
    compactExp2620 momentScalarGrow2622K01P004Input 20 = momentScalarGrow2622K01P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P004] using h

theorem momentScalarGrow2622K01P004_radius_le :
    (momentScalarGrow2622K01P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P004Expected]

end ConnesWeilRH.Dev
