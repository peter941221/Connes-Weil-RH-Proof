import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P178 : ℚ := ((-85532889748068301220937960837866450445931694706636609 : ℚ) / 618783237172668906432819882054828616378739798835200)

def momentPanelGrowth2622K01P178 : ℚ := ((635220948263565207207193923296034545084880008997375931 : ℚ) / 51407570788075839518877058390661294231450826257203200)

theorem momentPanelPhase_owner2622K01P178 :
    (momentPanelPhase2622K01P178 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (177 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P178, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P178 :
    (momentPanelGrowth2622K01P178 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P178, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P178Input : RatPair2542 := (momentPanelPhase2622K01P178 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P178Expected : RatState2542 :=
  ((((993361175460663658500542102454391055 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P178_replay :
    compactExp2620 momentScalarAmp2622K01P178Input 20 = momentScalarAmp2622K01P178Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P178_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (177 / 200) 0) -
      (momentScalarAmp2622K01P178Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P178]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P178 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P178 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P178Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P178_replay] at h
  simpa only [momentPanelPhase_owner2622K01P178] using h

theorem momentScalarAmp2622K01P178_radius_le :
    (momentScalarAmp2622K01P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P178Expected]

def momentScalarGrow2622K01P178Input : RatPair2542 := (momentPanelGrowth2622K01P178 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P178Expected : RatState2542 :=
  ((((496576605273059605502378059349914269598055646572153444225300742963536189655169963962751286423494354999 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((629478213831902963122853376684976788919857707268235583 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P178_replay :
    compactExp2620 momentScalarGrow2622K01P178Input 20 = momentScalarGrow2622K01P178Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P178_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P178Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P178]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P178 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P178 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P178Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P178_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P178] using h

theorem momentScalarGrow2622K01P178_radius_le :
    (momentScalarGrow2622K01P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P178Expected]

end ConnesWeilRH.Dev
