import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P148 : ℚ := ((-218392828104727561268217317728191211466140569828429525 : ℚ) / 4806696197476673335107143954199765316270905142280192)

def momentPanelGrowth2622K03P148 : ℚ := ((1081687985963456240496148915728802747719800612786115475 : ℚ) / 1293957555911301203559488872211843543010172105635397632)

theorem momentPanelPhase_owner2622K03P148 :
    (momentPanelPhase2622K03P148 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (117 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P148, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P148 :
    (momentPanelGrowth2622K03P148 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P148, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P148Input : RatPair2542 := (momentPanelPhase2622K03P148 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P148Expected : RatState2542 :=
  ((((39570892650007832611253669603640323127265685171499421051671896118864225424515 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((50166657255887143582635381807 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P148_replay :
    compactExp2620 momentScalarAmp2622K03P148Input 20 = momentScalarAmp2622K03P148Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P148_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (117 / 200) 0) -
      (momentScalarAmp2622K03P148Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P148]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P148 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P148 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P148Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P148_replay] at h
  simpa only [momentPanelPhase_owner2622K03P148] using h

theorem momentScalarAmp2622K03P148_radius_le :
    (momentScalarAmp2622K03P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P148Expected]

def momentScalarGrow2622K03P148Input : RatPair2542 := (momentPanelGrowth2622K03P148 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P148Expected : RatState2542 :=
  ((((615968489912768205494763760860557857489685202353436666258093714248804663730531524646697564129567 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((6246657627669943081740768871288407428575403667079 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P148_replay :
    compactExp2620 momentScalarGrow2622K03P148Input 20 = momentScalarGrow2622K03P148Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P148_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P148Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P148Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P148 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P148]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P148 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P148 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P148Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P148Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P148_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P148] using h

theorem momentScalarGrow2622K03P148_radius_le :
    (momentScalarGrow2622K03P148Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P148Expected]

end ConnesWeilRH.Dev
