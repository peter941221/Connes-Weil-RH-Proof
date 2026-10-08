import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P152 : ℚ := ((-6428970322422161849647366300286830555526651110625 : ℚ) / 148433760041419827630061740822747494183805648896)

def momentPanelGrowth2622K04P152 : ℚ := ((5886612024163092368863899028986126309138445680475608447 : ℚ) / 5191322466413386322129767429363367806533932402763366400)

theorem momentPanelPhase_owner2622K04P152 :
    (momentPanelPhase2622K04P152 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (5 / 8) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P152, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P152 :
    (momentPanelGrowth2622K04P152 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P152, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P152Input : RatPair2542 := (momentPanelPhase2622K04P152 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P152Expected : RatState2542 :=
  ((((330685103581018126076657822544909340946805698537609050303995996309895706354421 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((52401612908878825642551771229 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P152_replay :
    compactExp2620 momentScalarAmp2622K04P152Input 20 = momentScalarAmp2622K04P152Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P152_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (5 / 8) 0) -
      (momentScalarAmp2622K04P152Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P152]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P152 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P152 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P152Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P152_replay] at h
  simpa only [momentPanelPhase_owner2622K04P152] using h

theorem momentScalarAmp2622K04P152_radius_le :
    (momentScalarAmp2622K04P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P152Expected]

def momentScalarGrow2622K04P152Input : RatPair2542 := (momentPanelGrowth2622K04P152 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P152Expected : RatState2542 :=
  ((((6638339677838679166873668056093594269917246361345916923097263646958997988771716378645706779536839 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8415086177028321753798811655537259103226114618663 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P152_replay :
    compactExp2620 momentScalarGrow2622K04P152Input 20 = momentScalarGrow2622K04P152Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P152_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P152Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P152]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P152 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P152 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P152Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P152_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P152] using h

theorem momentScalarGrow2622K04P152_radius_le :
    (momentScalarGrow2622K04P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P152Expected]

end ConnesWeilRH.Dev
