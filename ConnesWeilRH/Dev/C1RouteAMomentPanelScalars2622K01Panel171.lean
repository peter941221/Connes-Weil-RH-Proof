import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P171 : ℚ := ((-28496468296735291878177228751576906854758496895461977 : ℚ) / 319489396012229119374897314261269486279277831782400)

def momentPanelGrowth2622K01P171 : ℚ := ((36588077521908685830013322415793961526998205162531251 : ℚ) / 7977850746726186298154474626282606726460229235507200)

theorem momentPanelPhase_owner2622K01P171 :
    (momentPanelPhase2622K01P171 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (163 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P171, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P171 :
    (momentPanelGrowth2622K01P171 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P171, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P171Input : RatPair2542 := (momentPanelPhase2622K01P171 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P171Expected : RatState2542 :=
  ((((3919496130972599947482962506744554380457465832985085916223 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229263318593773 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P171_replay :
    compactExp2620 momentScalarAmp2622K01P171Input 20 = momentScalarAmp2622K01P171Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P171_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (163 / 200) 0) -
      (momentScalarAmp2622K01P171Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P171]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P171 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P171 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P171Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P171_replay] at h
  simpa only [momentPanelPhase_owner2622K01P171] using h

theorem momentScalarAmp2622K01P171_radius_le :
    (momentScalarAmp2622K01P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P171Expected]

def momentScalarGrow2622K01P171Input : RatPair2542 := (momentPanelGrowth2622K01P171 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P171Expected : RatState2542 :=
  ((((104793211589548776866848688571723014571726275814014823158557858556730587086207541738200277582278361 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((132840596558753394813430645298148884056469960531313 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P171_replay :
    compactExp2620 momentScalarGrow2622K01P171Input 20 = momentScalarGrow2622K01P171Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P171_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P171Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P171]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P171 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P171 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P171Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P171_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P171] using h

theorem momentScalarGrow2622K01P171_radius_le :
    (momentScalarGrow2622K01P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P171Expected]

end ConnesWeilRH.Dev
