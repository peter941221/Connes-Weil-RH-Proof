import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P175 : ℚ := ((-85512623709810931655787881713336320542522700988413603 : ℚ) / 767787896291171118015304937265355908617098546380800)

def momentPanelGrowth2622K01P175 : ℚ := ((38366667695359617093814117490199937450746473526937891 : ℚ) / 5040574995137320862936522101155545735784536683315200)

theorem momentPanelPhase_owner2622K01P175 :
    (momentPanelPhase2622K01P175 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (171 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P175, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P175 :
    (momentPanelGrowth2622K01P175 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P175, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P175Input : RatPair2542 := (momentPanelPhase2622K01P175 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P175Expected : RatState2542 :=
  ((((56989012202175938282543121704348799735204208849 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((2417851639229258349412357 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P175_replay :
    compactExp2620 momentScalarAmp2622K01P175Input 20 = momentScalarAmp2622K01P175Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P175_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (171 / 200) 0) -
      (momentScalarAmp2622K01P175Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P175]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P175 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P175 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P175Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P175_replay] at h
  simpa only [momentPanelPhase_owner2622K01P175] using h

theorem momentScalarAmp2622K01P175_radius_le :
    (momentScalarAmp2622K01P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P175Expected]

def momentScalarGrow2622K01P175Input : RatPair2542 := (momentPanelGrowth2622K01P175 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P175Expected : RatState2542 :=
  ((((4317770856608991889874873875500200192104822363633143359920693354717140307257841768740954632172559231 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5473385086829702080077366155986534741939963147686631 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P175_replay :
    compactExp2620 momentScalarGrow2622K01P175Input 20 = momentScalarGrow2622K01P175Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P175_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P175Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P175Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P175 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P175]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P175 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P175 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P175Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P175Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P175_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P175] using h

theorem momentScalarGrow2622K01P175_radius_le :
    (momentScalarGrow2622K01P175Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P175Expected]

end ConnesWeilRH.Dev
