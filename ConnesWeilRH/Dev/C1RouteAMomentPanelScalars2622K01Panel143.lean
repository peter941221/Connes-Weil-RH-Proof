import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P143 : ℚ := ((-28477295482551880122053971960894888751254728317194913 : ℚ) / 679155814574131009401585378562542260647729981030400)

def momentPanelGrowth2622K01P143 : ℚ := ((72462803455500572114706495867347241772055789555604393 : ℚ) / 111911954513959337882658287607653599376285955103129600)

theorem momentPanelPhase_owner2622K01P143 :
    (momentPanelPhase2622K01P143 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (107 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P143 :
    (momentPanelGrowth2622K01P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P143Input : RatPair2542 := (momentPanelPhase2622K01P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P143Expected : RatState2542 :=
  ((((1316570591147534511055028431009020227441895399536149637639805932751600201030291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1669020657286827654888670258951 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P143_replay :
    compactExp2620 momentScalarAmp2622K01P143Input 20 = momentScalarAmp2622K01P143Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622K01P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P143]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P143 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P143_replay] at h
  simpa only [momentPanelPhase_owner2622K01P143] using h

theorem momentScalarAmp2622K01P143_radius_le :
    (momentScalarAmp2622K01P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P143Expected]

def momentScalarGrow2622K01P143Input : RatPair2542 := (momentPanelGrowth2622K01P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P143Expected : RatState2542 :=
  ((((4081347403990881047367857694721908930061327668522172822876539334915159231444286785569092572228719 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5173719291623250928463250554595550949133751663783 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P143_replay :
    compactExp2620 momentScalarGrow2622K01P143Input 20 = momentScalarGrow2622K01P143Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P143_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P143] using h

theorem momentScalarGrow2622K01P143_radius_le :
    (momentScalarGrow2622K01P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P143Expected]

end ConnesWeilRH.Dev
