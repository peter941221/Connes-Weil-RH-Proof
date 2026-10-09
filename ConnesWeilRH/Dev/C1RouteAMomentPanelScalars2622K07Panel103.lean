import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P103 : ℚ := ((-93882984191321729328162475567679874225 : ℚ) / 3186042030180018996875330021012537344)

def momentPanelGrowth2622K07P103 : ℚ := ((13657005375067534716435052280251087025 : ℚ) / 81229711823591099037660760881909202944)

theorem momentPanelPhase_owner2622K07P103 :
    (momentPanelPhase2622K07P103 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (27 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P103, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P103 :
    (momentPanelGrowth2622K07P103 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P103, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P103Input : RatPair2542 := (momentPanelPhase2622K07P103 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P103Expected : RatState2542 :=
  ((((170305617467345772580694815347622630891984772107662286269078236561174929110300640821 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((431788170303417445211366246495020131 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P103_replay :
    compactExp2620 momentScalarAmp2622K07P103Input 20 = momentScalarAmp2622K07P103Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P103_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (27 / 200) 0) -
      (momentScalarAmp2622K07P103Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P103]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P103 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P103 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P103Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P103_replay] at h
  simpa only [momentPanelPhase_owner2622K07P103] using h

theorem momentScalarAmp2622K07P103_radius_le :
    (momentScalarAmp2622K07P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P103Expected]

def momentScalarGrow2622K07P103Input : RatPair2542 := (momentPanelGrowth2622K07P103 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P103Expected : RatState2542 :=
  ((((631765304371600029434964936590885264152315535511243611708735224454648625421669710492953047460173 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3203430155523531468411111813400202674586213691371 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P103_replay :
    compactExp2620 momentScalarGrow2622K07P103Input 20 = momentScalarGrow2622K07P103Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P103_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P103Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P103Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P103 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P103]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P103 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P103 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P103Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P103Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P103_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P103] using h

theorem momentScalarGrow2622K07P103_radius_le :
    (momentScalarGrow2622K07P103Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P103Expected]

end ConnesWeilRH.Dev
