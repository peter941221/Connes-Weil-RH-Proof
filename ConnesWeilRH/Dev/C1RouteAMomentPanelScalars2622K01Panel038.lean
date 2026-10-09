import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P038 : ℚ := ((-28611999105973710777157282272490874180077658972237843 : ℚ) / 699137282272014447736401382134835192557088433766400)

def momentPanelGrowth2622K01P038 : ℚ := ((22721150199319552251134769331792871594000774523659 : ℚ) / 38642731280013863779653092622845080817562864844800)

theorem momentPanelPhase_owner2622K01P038 :
    (momentPanelPhase2622K01P038 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-103 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P038, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P038 :
    (momentPanelGrowth2622K01P038 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P038, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P038Input : RatPair2542 := (momentPanelPhase2622K01P038 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P038Expected : RatState2542 :=
  ((((3599295943518462273922508910294663826865632360709010457000014804057090858880131 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2281415079763029652770274211073 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P038_replay :
    compactExp2620 momentScalarAmp2622K01P038Input 20 = momentScalarAmp2622K01P038Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P038_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-103 / 200) 0) -
      (momentScalarAmp2622K01P038Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P038]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P038 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P038 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P038Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P038_replay] at h
  simpa only [momentPanelPhase_owner2622K01P038] using h

theorem momentScalarAmp2622K01P038_radius_le :
    (momentScalarAmp2622K01P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P038Expected]

def momentScalarGrow2622K01P038Input : RatPair2542 := (momentPanelGrowth2622K01P038 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P038Expected : RatState2542 :=
  ((((480689971793352631158650126480666763730874368461923598903862161685778239067998637817456640867411 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2437386358326431343827097772805915754310804407377 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P038_replay :
    compactExp2620 momentScalarGrow2622K01P038Input 20 = momentScalarGrow2622K01P038Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P038_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P038Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P038]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P038 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P038 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P038Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P038_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P038] using h

theorem momentScalarGrow2622K01P038_radius_le :
    (momentScalarGrow2622K01P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P038Expected]

end ConnesWeilRH.Dev
