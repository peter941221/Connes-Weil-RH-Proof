import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P142 : ℚ := ((-8736102640111910368604666362646055282846202670975625 : ℚ) / 211735049708314560274758840139771502472653227163648)

def momentPanelGrowth2622K03P142 : ℚ := ((972905793978075395529732744948112797898491396291627475 : ℚ) / 1574478180180594709679504139003406905802931797934211072)

theorem momentPanelPhase_owner2622K03P142 :
    (momentPanelPhase2622K03P142 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (21 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P142 :
    (momentPanelGrowth2622K03P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P142Input : RatPair2542 := (momentPanelPhase2622K03P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P142Expected : RatState2542 :=
  ((((160939889833350290173568428467169572533557728566163483982749691677350106052977 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1632189814957280996660103883007 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P142_replay :
    compactExp2620 momentScalarAmp2622K03P142Input 20 = momentScalarAmp2622K03P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K03P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P142_replay] at h
  simpa only [momentPanelPhase_owner2622K03P142] using h

theorem momentScalarAmp2622K03P142_radius_le :
    (momentScalarAmp2622K03P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P142Expected]

def momentScalarGrow2622K03P142Input : RatPair2542 := (momentPanelGrowth2622K03P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P142Expected : RatState2542 :=
  ((((1981203250036213136243400194143977085159025735274070327426477112189372615763500516777113976871333 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5022944018158336202023034447530688421671633215615 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P142_replay :
    compactExp2620 momentScalarGrow2622K03P142Input 20 = momentScalarGrow2622K03P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P142] using h

theorem momentScalarGrow2622K03P142_radius_le :
    (momentScalarGrow2622K03P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P142Expected]

end ConnesWeilRH.Dev
