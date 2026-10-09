import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P091 : ℚ := ((-96962649574419092048643619016868464025 : ℚ) / 3244455369838535807696298104716263424)

def momentPanelGrowth2622K07P091 : ℚ := ((7831665760458884281616762741727427025 : ℚ) / 84442445504809523632814005485614137344)

theorem momentPanelPhase_owner2622K07P091 :
    (momentPanelPhase2622K07P091 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P091, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P091 :
    (momentPanelGrowth2622K07P091 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P091, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P091Input : RatPair2542 := (momentPanelPhase2622K07P091 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P091Expected : RatState2542 :=
  ((((112046117172420582601869255589048837820101587130386843054955974175961481042631625089 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((284078751838829686731129799840761311 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P091_replay :
    compactExp2620 momentScalarAmp2622K07P091Input 20 = momentScalarAmp2622K07P091Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P091_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 200) 0) -
      (momentScalarAmp2622K07P091Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P091]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P091 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P091 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P091Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P091_replay] at h
  simpa only [momentPanelPhase_owner2622K07P091] using h

theorem momentScalarAmp2622K07P091_radius_le :
    (momentScalarAmp2622K07P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P091Expected]

def momentScalarGrow2622K07P091Input : RatPair2542 := (momentPanelGrowth2622K07P091 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P091Expected : RatState2542 :=
  ((((2343567772976498908697837798172554454491867361500091450378151624056461285904359827259102034637361 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2970824831322393080606911888073070155382165992273 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P091_replay :
    compactExp2620 momentScalarGrow2622K07P091Input 20 = momentScalarGrow2622K07P091Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P091_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P091Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P091]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P091 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P091 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P091Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P091_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P091] using h

theorem momentScalarGrow2622K07P091_radius_le :
    (momentScalarGrow2622K07P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P091Expected]

end ConnesWeilRH.Dev
