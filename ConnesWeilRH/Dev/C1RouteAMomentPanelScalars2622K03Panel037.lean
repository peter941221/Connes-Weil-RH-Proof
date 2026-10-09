import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P037 : ℚ := ((-8801917007858924649839551629949340953024987844736375 : ℚ) / 211735049708314560274758840139771502472653227163648)

def momentPanelGrowth2622K03P037 : ℚ := ((972905793978075395529732744948112797898491396291627475 : ℚ) / 1574478180180594709679504139003406905802931797934211072)

theorem momentPanelPhase_owner2622K03P037 :
    (momentPanelPhase2622K03P037 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-21 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P037 :
    (momentPanelGrowth2622K03P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P037Input : RatPair2542 := (momentPanelPhase2622K03P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P037Expected : RatState2542 :=
  ((((471770057853688046254342949500571408394529627186060516417390048511400385208685 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((598063911012027748043935141163 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P037_replay :
    compactExp2620 momentScalarAmp2622K03P037Input 20 = momentScalarAmp2622K03P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K03P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P037_replay] at h
  simpa only [momentPanelPhase_owner2622K03P037] using h

theorem momentScalarAmp2622K03P037_radius_le :
    (momentScalarAmp2622K03P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P037Expected]

def momentScalarGrow2622K03P037Input : RatPair2542 := (momentPanelGrowth2622K03P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P037Expected : RatState2542 :=
  ((((1981203250036213136243400194143977085159025735274070327426477112189372615763500516777113976871333 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5022944018158336202023034447530688421671633215615 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P037_replay :
    compactExp2620 momentScalarGrow2622K03P037Input 20 = momentScalarGrow2622K03P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P037] using h

theorem momentScalarGrow2622K03P037_radius_le :
    (momentScalarGrow2622K03P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P037Expected]

end ConnesWeilRH.Dev
