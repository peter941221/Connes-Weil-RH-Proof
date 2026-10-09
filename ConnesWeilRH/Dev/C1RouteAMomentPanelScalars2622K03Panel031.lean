import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P031 : ℚ := ((-220057663094543314192888132086693694430639193064370475 : ℚ) / 4806696197476673335107143954199765316270905142280192)

def momentPanelGrowth2622K03P031 : ℚ := ((1081687985963456240496148915728802747719800612786115475 : ℚ) / 1293957555911301203559488872211843543010172105635397632)

theorem momentPanelPhase_owner2622K03P031 :
    (momentPanelPhase2622K03P031 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-117 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P031, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P031 :
    (momentPanelGrowth2622K03P031 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-117 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P031, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P031Input : RatPair2542 := (momentPanelPhase2622K03P031 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P031Expected : RatState2542 :=
  ((((27986895251929758993962893766549588354955337114937526014640189076154850029339 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((35481571424338645041700279353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P031_replay :
    compactExp2620 momentScalarAmp2622K03P031Input 20 = momentScalarAmp2622K03P031Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P031_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-117 / 200) 0) -
      (momentScalarAmp2622K03P031Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P031]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P031 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P031 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P031Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P031_replay] at h
  simpa only [momentPanelPhase_owner2622K03P031] using h

theorem momentScalarAmp2622K03P031_radius_le :
    (momentScalarAmp2622K03P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P031Expected]

def momentScalarGrow2622K03P031Input : RatPair2542 := (momentPanelGrowth2622K03P031 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P031Expected : RatState2542 :=
  ((((615968489912768205494763760860557857489685202353436666258093714248804663730531524646697564129567 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((6246657627669943081740768871288407428575403667079 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P031_replay :
    compactExp2620 momentScalarGrow2622K03P031Input 20 = momentScalarGrow2622K03P031Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P031_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-117 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P031Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P031Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P031 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P031]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P031 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P031 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P031Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P031Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P031_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P031] using h

theorem momentScalarGrow2622K03P031_radius_le :
    (momentScalarGrow2622K03P031Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P031Expected]

end ConnesWeilRH.Dev
