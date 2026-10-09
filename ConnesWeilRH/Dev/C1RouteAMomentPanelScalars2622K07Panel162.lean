import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P162 : ℚ := ((-1177929326615144815599258901654662625 : ℚ) / 20525798518895490469034618301448192)

def momentPanelGrowth2622K07P162 : ℚ := ((616064906805321250020066798134449638025 : ℚ) / 295017667195457750241502199897238011904)

theorem momentPanelPhase_owner2622K07P162 :
    (momentPanelPhase2622K07P162 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P162 :
    (momentPanelGrowth2622K07P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P162Input : RatPair2542 := (momentPanelPhase2622K07P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P162Expected : RatState2542 :=
  ((((127463807641368068303830235650950321834449759077828640903797112027265293 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2741028470490782189176437 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P162_replay :
    compactExp2620 momentScalarAmp2622K07P162Input 20 = momentScalarAmp2622K07P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K07P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P162_replay] at h
  simpa only [momentPanelPhase_owner2622K07P162] using h

theorem momentScalarAmp2622K07P162_radius_le :
    (momentScalarAmp2622K07P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P162Expected]

def momentScalarGrow2622K07P162Input : RatPair2542 := (momentPanelGrowth2622K07P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P162Expected : RatState2542 :=
  ((((2154842994983228281969607451471910484221791884020698182064347660892957990680779464153406303984669 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((21852660608465913910827680283740071642873557917719 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P162_replay :
    compactExp2620 momentScalarGrow2622K07P162Input 20 = momentScalarGrow2622K07P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P162] using h

theorem momentScalarGrow2622K07P162_radius_le :
    (momentScalarGrow2622K07P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P162Expected]

end ConnesWeilRH.Dev
