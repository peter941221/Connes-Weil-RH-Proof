import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P014 : ℚ := ((-35287002894657525808610768193129124225 : ℚ) / 465116217030940106161958366490918912)

def momentPanelGrowth2622K07P014 : ℚ := ((38822217165673626030277019876305225 : ℚ) / 14725029372251112727785704433647616)

theorem momentPanelPhase_owner2622K07P014 :
    (momentPanelPhase2622K07P014 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P014 :
    (momentPanelGrowth2622K07P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P014Input : RatPair2542 := (momentPanelPhase2622K07P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P014Expected : RatState2542 :=
  ((((1202043947074579676281257674464676608391749237787361090913472067 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((302231455284627809868183 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K07P014_replay :
    compactExp2620 momentScalarAmp2622K07P014Input 20 = momentScalarAmp2622K07P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K07P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P014_replay] at h
  simpa only [momentPanelPhase_owner2622K07P014] using h

theorem momentScalarAmp2622K07P014_radius_le :
    (momentScalarAmp2622K07P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P014Expected]

def momentScalarGrow2622K07P014Input : RatPair2542 := (momentPanelGrowth2622K07P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P014Expected : RatState2542 :=
  ((((466043569840293624544232509583586901391442955630286094374701618183981694983334840950646132159539 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((37809851239600547906943294047715376505322669180893 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P014_replay :
    compactExp2620 momentScalarGrow2622K07P014Input 20 = momentScalarGrow2622K07P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P014] using h

theorem momentScalarGrow2622K07P014_radius_le :
    (momentScalarGrow2622K07P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P014Expected]

end ConnesWeilRH.Dev
