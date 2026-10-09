import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P154 : ℚ := ((-324956089605613605732895970621323187386133575644714831 : ℚ) / 6667815770783703372328100392074151378152915678003200)

def momentPanelGrowth2622K02P154 : ℚ := ((3072466400815244512165008744808871952710614062696373 : ℚ) / 2538645471016090840438373253859816999083991420108800)

theorem momentPanelPhase_owner2622K02P154 :
    (momentPanelPhase2622K02P154 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (129 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P154, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P154 :
    (momentPanelGrowth2622K02P154 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P154, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P154Input : RatPair2542 := (momentPanelPhase2622K02P154 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P154Expected : RatState2542 :=
  ((((729829323116513623146321486979615580046039417138219283535158410875122242371 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1852841011394993254376432827 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P154_replay :
    compactExp2620 momentScalarAmp2622K02P154Input 20 = momentScalarAmp2622K02P154Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P154_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (129 / 200) 0) -
      (momentScalarAmp2622K02P154Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P154]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P154 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P154 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P154Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P154_replay] at h
  simpa only [momentPanelPhase_owner2622K02P154] using h

theorem momentScalarAmp2622K02P154_radius_le :
    (momentScalarAmp2622K02P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P154Expected]

def momentScalarGrow2622K02P154Input : RatPair2542 := (momentPanelGrowth2622K02P154 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P154Expected : RatState2542 :=
  ((((3582495155243660895800082172817948874646610482007154246664943160366306484024347000837147983425079 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1135336723046051301938169850339409839393805875899 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P154_replay :
    compactExp2620 momentScalarGrow2622K02P154Input 20 = momentScalarGrow2622K02P154Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P154_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P154Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P154]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P154 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P154 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P154Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P154_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P154] using h

theorem momentScalarGrow2622K02P154_radius_le :
    (momentScalarGrow2622K02P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P154Expected]

end ConnesWeilRH.Dev
