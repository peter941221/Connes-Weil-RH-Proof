import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K26
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K26P063 : ℚ := ((-821616328704758279247641098055032413129 : ℚ) / 25144103185646975824567407419274035200)

def momentPanelGrowth2622K26P063 : ℚ := ((17778765105157649187323241613323282046729 : ℚ) / 87165116619304996749767357801108917452800)

theorem momentPanelPhase_owner2622K26P063 :
    (momentPanelPhase2622K26P063 : ℝ) = momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (-53 / 200) 0 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P063, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K26P063 :
    (momentPanelGrowth2622K26P063 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2))
      (-53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P063, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K26P063Input : RatPair2542 := (momentPanelPhase2622K26P063 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K26P063Expected : RatState2542 :=
  ((((429843783141261854055980642135254863382543917929291204757370014684340887649770925 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((17437078728309979185698112983363365 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K26P063_replay :
    compactExp2620 momentScalarAmp2622K26P063Input 20 = momentScalarAmp2622K26P063Expected := by
  decide +kernel

theorem momentScalarAmp2622K26P063_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (-53 / 200) 0) -
      (momentScalarAmp2622K26P063Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K26P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K26P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelPhase2622K26P063]
  have h := compactExp_real_error2620 momentPanelPhase2622K26P063 20 hsmall
  change |Real.exp (momentPanelPhase2622K26P063 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K26P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K26P063Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K26P063_replay] at h
  simpa only [momentPanelPhase_owner2622K26P063] using h

theorem momentScalarAmp2622K26P063_radius_le :
    (momentScalarAmp2622K26P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarAmp2622K26P063Expected]

def momentScalarGrow2622K26P063Input : RatPair2542 := (momentPanelGrowth2622K26P063 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K26P063Expected : RatState2542 :=
  ((((1309634625710667606088938954087466252190781643610153484037097699872270602112260537016568022025275 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((830079398215809566463348591501389503583055414339 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K26P063_replay :
    compactExp2620 momentScalarGrow2622K26P063Input 20 = momentScalarGrow2622K26P063Expected := by
  decide +kernel

theorem momentScalarGrow2622K26P063_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 26).re * (storedWidth 26 ^ 2)) (-53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K26P063Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K26P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K26P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentPanelGrowth2622K26P063]
  have h := compactExp_real_error2620 momentPanelGrowth2622K26P063 20 hsmall
  change |Real.exp (momentPanelGrowth2622K26P063 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K26P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K26P063Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K26P063_replay] at h
  simpa only [momentPanelGrowth_owner2622K26P063] using h

theorem momentScalarGrow2622K26P063_radius_le :
    (momentScalarGrow2622K26P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, momentScalarGrow2622K26P063Expected]

end ConnesWeilRH.Dev
