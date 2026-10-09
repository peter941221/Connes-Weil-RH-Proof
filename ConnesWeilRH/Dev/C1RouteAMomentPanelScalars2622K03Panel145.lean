import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P145 : ℚ := ((-218394455414251787949446914422955298623226464602971175 : ℚ) / 5056612977460257734119974060594249712632069607129088)

def momentPanelGrowth2622K03P145 : ℚ := ((4012882199826394249447758446876741055475609911408475 : ℚ) / 5603671309083681332690090839540363400427030857121792)

theorem momentPanelPhase_owner2622K03P145 :
    (momentPanelPhase2622K03P145 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (111 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P145, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P145 :
    (momentPanelGrowth2622K03P145 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P145, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P145Input : RatPair2542 := (momentPanelPhase2622K03P145 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P145Expected : RatState2542 :=
  ((((373659944793307238140623893445940762039847216004769672978176316747591535754203 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((473692181588876636998178536273 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P145_replay :
    compactExp2620 momentScalarAmp2622K03P145Input 20 = momentScalarAmp2622K03P145Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P145_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (111 / 200) 0) -
      (momentScalarAmp2622K03P145Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P145]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P145 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P145 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P145Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P145_replay] at h
  simpa only [momentPanelPhase_owner2622K03P145] using h

theorem momentScalarAmp2622K03P145_radius_le :
    (momentScalarAmp2622K03P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P145Expected]

def momentScalarGrow2622K03P145Input : RatPair2542 := (momentPanelGrowth2622K03P145 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P145Expected : RatState2542 :=
  ((((2185617284583756761052337491750051713713709334507109947076319799369102933093926634987410274170273 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2770597170513875559318686813901239584590451591731 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P145_replay :
    compactExp2620 momentScalarGrow2622K03P145Input 20 = momentScalarGrow2622K03P145Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P145_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P145Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P145]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P145 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P145 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P145Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P145_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P145] using h

theorem momentScalarGrow2622K03P145_radius_le :
    (momentScalarGrow2622K03P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P145Expected]

end ConnesWeilRH.Dev
