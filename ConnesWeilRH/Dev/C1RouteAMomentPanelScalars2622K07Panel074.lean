import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P074 : ℚ := ((-33773016828602710934028675901700773225 : ℚ) / 1055739984689276748907302323939704832)

def momentPanelGrowth2622K07P074 : ℚ := ((911943763904042903845112717021934025 : ℚ) / 5014906904141290119002653669472600064)

theorem momentPanelPhase_owner2622K07P074 :
    (momentPanelPhase2622K07P074 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-31 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P074 :
    (momentPanelGrowth2622K07P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P074Input : RatPair2542 := (momentPanelPhase2622K07P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P074Expected : RatState2542 :=
  ((((13662540108354878864028749473739125162429153584633978792042211759676907283928607175 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((34639711110740062248658022319356277 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P074_replay :
    compactExp2620 momentScalarAmp2622K07P074Input 20 = momentScalarAmp2622K07P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K07P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P074_replay] at h
  simpa only [momentPanelPhase_owner2622K07P074] using h

theorem momentScalarAmp2622K07P074_radius_le :
    (momentScalarAmp2622K07P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P074Expected]

def momentScalarGrow2622K07P074Input : RatPair2542 := (momentPanelGrowth2622K07P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P074Expected : RatState2542 :=
  ((((20015369744303144770852874722340905378359112812858731118484476773790846559749213626278171052509 : ℚ) / 16687398718132110018711107079449625895333629080911349765211262561111091607661254297054391304192), 0), ((3247678856959534793403239281148612415552375996609 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P074_replay :
    compactExp2620 momentScalarGrow2622K07P074Input 20 = momentScalarGrow2622K07P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P074] using h

theorem momentScalarGrow2622K07P074_radius_le :
    (momentScalarGrow2622K07P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P074Expected]

end ConnesWeilRH.Dev
