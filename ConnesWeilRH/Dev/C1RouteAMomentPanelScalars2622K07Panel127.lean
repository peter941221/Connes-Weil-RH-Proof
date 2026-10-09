import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P127 : ℚ := ((-28451872125304271059038333732808701 : ℚ) / 892426022560673498653679056584704)

def momentPanelGrowth2622K07P127 : ℚ := ((24263077449251427797725381990520725025 : ℚ) / 61865689726792776250509841134124007424)

theorem momentPanelPhase_owner2622K07P127 :
    (momentPanelPhase2622K07P127 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 8) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P127, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P127 :
    (momentPanelGrowth2622K07P127 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (3 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P127, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P127Input : RatPair2542 := (momentPanelPhase2622K07P127 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P127Expected : RatState2542 :=
  ((((30453908307875015260458541554925365417140397879607130583728482880644628989706753809 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((38606088931457290150190136504947693 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P127_replay :
    compactExp2620 momentScalarAmp2622K07P127Input 20 = momentScalarAmp2622K07P127Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P127_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 8) 0) -
      (momentScalarAmp2622K07P127Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P127]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P127 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P127 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P127Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P127_replay] at h
  simpa only [momentPanelPhase_owner2622K07P127] using h

theorem momentScalarAmp2622K07P127_radius_le :
    (momentScalarAmp2622K07P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P127Expected]

def momentScalarGrow2622K07P127Input : RatPair2542 := (momentPanelGrowth2622K07P127 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P127Expected : RatState2542 :=
  ((((395215879538728797208522595029949481346233151690877795619861916193686043693196165415945818891407 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2003981838136341620617813113313988480907978667277 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P127_replay :
    compactExp2620 momentScalarGrow2622K07P127Input 20 = momentScalarGrow2622K07P127Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P127_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (3 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P127Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P127Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P127 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P127]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P127 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P127 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P127Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P127Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P127_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P127] using h

theorem momentScalarGrow2622K07P127_radius_le :
    (momentScalarGrow2622K07P127Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P127Expected]

end ConnesWeilRH.Dev
