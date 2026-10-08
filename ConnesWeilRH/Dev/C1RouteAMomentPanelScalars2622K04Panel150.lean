import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P150 : ℚ := ((-100355508516029322723740480535499243219437636720263549 : ℚ) / 2412904949288695774917138259951316477568671442534400)

def momentPanelGrowth2622K04P150 : ℚ := ((1918868308935652215081926571549163688662017228872372069 : ℚ) / 1875681353341401134099429812134888425909982784703692800)

theorem momentPanelPhase_owner2622K04P150 :
    (momentPanelPhase2622K04P150 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (121 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P150, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P150 :
    (momentPanelGrowth2622K04P150 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (121 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P150, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P150Input : RatPair2542 := (momentPanelPhase2622K04P150 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P150Expected : RatState2542 :=
  ((((924184426257540576344605492414675182531500788189330414584994447616242024624083 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2343181242167153853628679516839 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P150_replay :
    compactExp2620 momentScalarAmp2622K04P150Input 20 = momentScalarAmp2622K04P150Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P150_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (121 / 200) 0) -
      (momentScalarAmp2622K04P150Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P150]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P150 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P150 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P150Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P150_replay] at h
  simpa only [momentPanelPhase_owner2622K04P150] using h

theorem momentScalarAmp2622K04P150_radius_le :
    (momentScalarAmp2622K04P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P150Expected]

def momentScalarGrow2622K04P150Input : RatPair2542 := (momentPanelGrowth2622K04P150 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P150Expected : RatState2542 :=
  ((((1485362970127964238263356545061578332481780102037723937668856287132526486882339365097866020268299 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1882919423601484986035227081920405352325453866697 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P150_replay :
    compactExp2620 momentScalarGrow2622K04P150Input 20 = momentScalarGrow2622K04P150Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P150_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (121 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P150Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P150Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P150 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P150]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P150 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P150 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P150Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P150Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P150_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P150] using h

theorem momentScalarGrow2622K04P150_radius_le :
    (momentScalarGrow2622K04P150Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P150Expected]

end ConnesWeilRH.Dev
