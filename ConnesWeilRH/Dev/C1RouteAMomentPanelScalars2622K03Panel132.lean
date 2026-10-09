import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P132 : ℚ := ((-2912959005423288044072147128541237117750621915405375 : ℚ) / 79834526939200571906876283987126959948705315160064)

def momentPanelGrowth2622K03P132 : ℚ := ((791545636415504394811405938987955960236078632328859475 : ℚ) / 2022925342579208961101122793074071187554158139420966912)

theorem momentPanelPhase_owner2622K03P132 :
    (momentPanelPhase2622K03P132 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (17 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P132, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P132 :
    (momentPanelGrowth2622K03P132 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P132, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P132Input : RatPair2542 := (momentPanelPhase2622K03P132 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P132Expected : RatState2542 :=
  ((((152148137319773315218489195769644532512879968140618313686128379135184077709270079 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((385754780546089141895418844059543 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P132_replay :
    compactExp2620 momentScalarAmp2622K03P132Input 20 = momentScalarAmp2622K03P132Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P132_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (17 / 40) 0) -
      (momentScalarAmp2622K03P132Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P132]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P132 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P132 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P132Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P132_replay] at h
  simpa only [momentPanelPhase_owner2622K03P132] using h

theorem momentScalarAmp2622K03P132_radius_le :
    (momentScalarAmp2622K03P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P132Expected]

def momentScalarGrow2622K03P132Input : RatPair2542 := (momentPanelGrowth2622K03P132 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P132Expected : RatState2542 :=
  ((((1579438316690831943569820174672777391291277543021116744220114659501890387527637429337601527007187 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4004350366085727140001133524985609929100269306051 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P132_replay :
    compactExp2620 momentScalarGrow2622K03P132Input 20 = momentScalarGrow2622K03P132Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P132_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P132Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P132Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P132 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P132]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P132 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P132 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P132Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P132Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P132_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P132] using h

theorem momentScalarGrow2622K03P132_radius_le :
    (momentScalarGrow2622K03P132Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P132Expected]

end ConnesWeilRH.Dev
