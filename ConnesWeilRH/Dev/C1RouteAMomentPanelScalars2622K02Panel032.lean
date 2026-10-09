import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P032 : ℚ := ((-961351580232472590925042815000668066732997891482269 : ℚ) / 20381097051841107101512323643738790547545621790720)

def momentPanelGrowth2622K02P032 : ℚ := ((108828853416371497291085345073161353031090628339911933 : ℚ) / 130939556897615065579966012209414197448621408701644800)

theorem momentPanelPhase_owner2622K02P032 :
    (momentPanelPhase2622K02P032 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-23 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P032, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P032 :
    (momentPanelGrowth2622K02P032 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P032, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P032Input : RatPair2542 := (momentPanelPhase2622K02P032 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P032Expected : RatState2542 :=
  ((((436853365400072316870128780879981479933606847023333465823463800257460363531 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((8863255329340295912348085293 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P032_replay :
    compactExp2620 momentScalarAmp2622K02P032Input 20 = momentScalarAmp2622K02P032Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P032_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-23 / 40) 0) -
      (momentScalarAmp2622K02P032Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P032]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P032 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P032 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P032Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P032_replay] at h
  simpa only [momentPanelPhase_owner2622K02P032] using h

theorem momentScalarAmp2622K02P032_radius_le :
    (momentScalarAmp2622K02P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P032Expected]

def momentScalarGrow2622K02P032Input : RatPair2542 := (momentPanelGrowth2622K02P032 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P032Expected : RatState2542 :=
  ((((613009651503033391571022891488539386509756332592262269301038737003135173796475653877620655141463 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((6216651493850316107999343167622244052392245873159 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P032_replay :
    compactExp2620 momentScalarGrow2622K02P032Input 20 = momentScalarGrow2622K02P032Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P032_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P032Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P032Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P032 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P032]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P032 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P032 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P032Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P032Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P032_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P032] using h

theorem momentScalarGrow2622K02P032_radius_le :
    (momentScalarGrow2622K02P032Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P032Expected]

end ConnesWeilRH.Dev
