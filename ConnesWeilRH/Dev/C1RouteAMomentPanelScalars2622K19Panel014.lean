import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K19
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K19P014 : ℚ := ((-824893405588262511213467032612723732027 : ℚ) / 11627905425773502654048959162272972800)

def momentPanelGrowth2622K19P014 : ℚ := ((946535961229824641267708094562628947 : ℚ) / 368125734306277818194642610841190400)

theorem momentPanelPhase_owner2622K19P014 :
    (momentPanelPhase2622K19P014 : ℝ) = momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K19P014 :
    (momentPanelGrowth2622K19P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K19P014Input : RatPair2542 := (momentPanelPhase2622K19P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K19P014Expected : RatState2542 :=
  ((((331422692609216513700573561385728854685158619315994225549061787765 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417852059385859975604373 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K19P014_replay :
    compactExp2620 momentScalarAmp2622K19P014Input 20 = momentScalarAmp2622K19P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K19P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K19P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K19P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K19P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelPhase2622K19P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K19P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K19P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K19P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K19P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K19P014_replay] at h
  simpa only [momentPanelPhase_owner2622K19P014] using h

theorem momentScalarAmp2622K19P014_radius_le :
    (momentScalarAmp2622K19P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarAmp2622K19P014Expected]

def momentScalarGrow2622K19P014Input : RatPair2542 := (momentPanelGrowth2622K19P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K19P014Expected : RatState2542 :=
  ((((27942782342681530346951419293675736686255609165839057248078353636614798622401322162435252294305865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4427699743846286885347613671761736936420704624175 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K19P014_replay :
    compactExp2620 momentScalarGrow2622K19P014Input 20 = momentScalarGrow2622K19P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K19P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 19).re * (storedWidth 19 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K19P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K19P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K19P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentPanelGrowth2622K19P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K19P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K19P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K19P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K19P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K19P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K19P014] using h

theorem momentScalarGrow2622K19P014_radius_le :
    (momentScalarGrow2622K19P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, momentScalarGrow2622K19P014Expected]

end ConnesWeilRH.Dev
