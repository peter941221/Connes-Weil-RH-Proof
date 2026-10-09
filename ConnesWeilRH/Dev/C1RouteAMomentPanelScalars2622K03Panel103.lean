import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P103 : ℚ := ((-218938528425690694965294785624927896261808842952269275 : ℚ) / 7174328849952736062597113383200143808113515861901312)

def momentPanelGrowth2622K03P103 : ℚ := ((16526655318334937720326515814656764468716481612544475 : ℚ) / 182913049950068823369161134744679819345084766970970112)

theorem momentPanelPhase_owner2622K03P103 :
    (momentPanelPhase2622K03P103 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (27 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P103 :
    (momentPanelGrowth2622K03P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P103Input : RatPair2542 := (momentPanelPhase2622K03P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P103Expected : RatState2542 :=
  ((((59598052230448353369803699255146436423328480120896385397370946108536460198646015953 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((151103410898549428601480244543705361 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P103_replay :
    compactExp2620 momentScalarAmp2622K03P103Input 20 = momentScalarAmp2622K03P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K03P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P103_replay] at h
  simpa only [momentPanelPhase_owner2622K03P103] using h

theorem momentScalarAmp2622K03P103_radius_le :
    (momentScalarAmp2622K03P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P103Expected]

def momentScalarGrow2622K03P103Input : RatPair2542 := (momentPanelGrowth2622K03P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P103Expected : RatState2542 :=
  ((((18265360340745113991648841280224853793412171918265653096233730017975811472428770837491205875313 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((740930976134861303848984861925817094791612434459 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P103_replay :
    compactExp2620 momentScalarGrow2622K03P103Input 20 = momentScalarGrow2622K03P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P103] using h

theorem momentScalarGrow2622K03P103_radius_le :
    (momentScalarGrow2622K03P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P103Expected]

end ConnesWeilRH.Dev
