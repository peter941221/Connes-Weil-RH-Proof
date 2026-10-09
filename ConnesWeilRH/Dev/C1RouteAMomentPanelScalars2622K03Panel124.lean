import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P124 : ℚ := ((-218567753332707644880829677890389437715764528963008325 : ℚ) / 6437732024737960991822456227511137166206925860241408)

def momentPanelGrowth2622K03P124 : ℚ := ((1034155951753336449199184145925121490303925247032675 : ℚ) / 3751217983766761883866920314072474673013136358899712)

theorem momentPanelPhase_owner2622K03P124 :
    (momentPanelPhase2622K03P124 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (69 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P124, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P124 :
    (momentPanelGrowth2622K03P124 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P124, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P124Input : RatPair2542 := (momentPanelPhase2622K03P124 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P124Expected : RatState2542 :=
  ((((1922275019243737330538449624780193756158034168364444822893415138521165890883846083 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1218425991432803993925861641278775 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P124_replay :
    compactExp2620 momentScalarAmp2622K03P124Input 20 = momentScalarAmp2622K03P124Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P124_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (69 / 200) 0) -
      (momentScalarAmp2622K03P124Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P124]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P124 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P124 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P124Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P124_replay] at h
  simpa only [momentPanelPhase_owner2622K03P124] using h

theorem momentScalarAmp2622K03P124_radius_le :
    (momentScalarAmp2622K03P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P124Expected]

def momentScalarGrow2622K03P124Input : RatPair2542 := (momentPanelGrowth2622K03P124 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P124Expected : RatState2542 :=
  ((((2814020463796904012928293791630454171964068773229670643343023972914551359561422450303527463562423 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3567193792121120647429691134273922197960575637287 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P124_replay :
    compactExp2620 momentScalarGrow2622K03P124Input 20 = momentScalarGrow2622K03P124Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P124_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P124Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P124Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P124 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P124]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P124 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P124 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P124Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P124Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P124_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P124] using h

theorem momentScalarGrow2622K03P124_radius_le :
    (momentScalarGrow2622K03P124Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P124Expected]

end ConnesWeilRH.Dev
