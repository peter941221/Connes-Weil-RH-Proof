import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P141 : ℚ := ((-28477908602264684465174156505488931275232205987762157 : ℚ) / 699137282272014447736401382134835192557088433766400)

def momentPanelGrowth2622K01P141 : ℚ := ((22721150199319552251134769331792871594000774523659 : ℚ) / 38642731280013863779653092622845080817562864844800)

theorem momentPanelPhase_owner2622K01P141 :
    (momentPanelPhase2622K01P141 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (103 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P141, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P141 :
    (momentPanelGrowth2622K01P141 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P141, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P141Input : RatPair2542 := (momentPanelPhase2622K01P141 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P141Expected : RatState2542 :=
  ((((2180131758232289765944397765214402498161452978026247134766566855517728054005287 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2763753899331722687881861718689 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P141_replay :
    compactExp2620 momentScalarAmp2622K01P141Input 20 = momentScalarAmp2622K01P141Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P141_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (103 / 200) 0) -
      (momentScalarAmp2622K01P141Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P141]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P141 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P141 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P141Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P141_replay] at h
  simpa only [momentPanelPhase_owner2622K01P141] using h

theorem momentScalarAmp2622K01P141_radius_le :
    (momentScalarAmp2622K01P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P141Expected]

def momentScalarGrow2622K01P141Input : RatPair2542 := (momentPanelGrowth2622K01P141 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P141Expected : RatState2542 :=
  ((((480689971793352631158650126480666763730874368461923598903862161685778239067998637817456640867411 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2437386358326431343827097772805915754310804407377 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P141_replay :
    compactExp2620 momentScalarGrow2622K01P141Input 20 = momentScalarGrow2622K01P141Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P141_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P141Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P141]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P141 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P141 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P141Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P141_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P141] using h

theorem momentScalarGrow2622K01P141_radius_le :
    (momentScalarGrow2622K01P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P141Expected]

end ConnesWeilRH.Dev
