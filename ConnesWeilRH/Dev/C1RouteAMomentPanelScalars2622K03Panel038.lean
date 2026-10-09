import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P038 : ℚ := ((-73347947169820557340668614902046698910839605536471675 : ℚ) / 1789791442616356986205187538265178092946146390441984)

def momentPanelGrowth2622K03P038 : ℚ := ((58274788332852517438124675489860547347257961764275 : ℚ) / 98925392076835491275911917114483406892960934002688)

theorem momentPanelPhase_owner2622K03P038 :
    (momentPanelPhase2622K03P038 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-103 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P038, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P038 :
    (momentPanelGrowth2622K03P038 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P038, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P038Input : RatPair2542 := (momentPanelPhase2622K03P038 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P038Expected : RatState2542 :=
  ((((1700686026280461791913257493470892705245071966429395103728639666123256187114877 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4311922260469390152447049406747 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P038_replay :
    compactExp2620 momentScalarAmp2622K03P038Input 20 = momentScalarAmp2622K03P038Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P038_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-103 / 200) 0) -
      (momentScalarAmp2622K03P038Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P038]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P038 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P038 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P038Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P038_replay] at h
  simpa only [momentPanelPhase_owner2622K03P038] using h

theorem momentScalarAmp2622K03P038_radius_le :
    (momentScalarAmp2622K03P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P038Expected]

def momentScalarGrow2622K03P038Input : RatPair2542 := (momentPanelGrowth2622K03P038 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P038Expected : RatState2542 :=
  ((((962436349483375572291199561126149559771205846362748934759566437934026766615980736670899914899945 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1220032330703478793150939127427121909280565454001 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P038_replay :
    compactExp2620 momentScalarGrow2622K03P038Input 20 = momentScalarGrow2622K03P038Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P038_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P038Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P038]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P038 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P038 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P038Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P038_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P038] using h

theorem momentScalarGrow2622K03P038_radius_le :
    (momentScalarGrow2622K03P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P038Expected]

end ConnesWeilRH.Dev
