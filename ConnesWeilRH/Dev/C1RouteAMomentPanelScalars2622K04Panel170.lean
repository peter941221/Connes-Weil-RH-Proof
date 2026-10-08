import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P170 : ℚ := ((-103967515575067075748417426741450701268750172429819029 : ℚ) / 1339614684373813944361307210925296135008845981286400)

def momentPanelGrowth2622K04P170 : ℚ := ((7096273358984994484186049178048257012020955364229019967 : ℚ) / 1687966025952712255046953289889370256885569353573990400)

theorem momentPanelPhase_owner2622K04P170 :
    (momentPanelPhase2622K04P170 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (161 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P170 :
    (momentPanelGrowth2622K04P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P170Input : RatPair2542 := (momentPanelPhase2622K04P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P170Expected : RatState2542 :=
  ((((420724122951048156663930870413122112081427328782349791101777761 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639762629080065689 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P170_replay :
    compactExp2620 momentScalarAmp2622K04P170Input 20 = momentScalarAmp2622K04P170Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622K04P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P170]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P170 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P170_replay] at h
  simpa only [momentPanelPhase_owner2622K04P170] using h

theorem momentScalarAmp2622K04P170_radius_le :
    (momentScalarAmp2622K04P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P170Expected]

def momentScalarGrow2622K04P170Input : RatPair2542 := (momentPanelGrowth2622K04P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P170Expected : RatState2542 :=
  ((((558662040623249271371820732382780745010412425863264335576930915321329865175585543224380573641619 : ℚ) / 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096), 0), ((90647735270300311278276459946466448749190289387457 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P170_replay :
    compactExp2620 momentScalarGrow2622K04P170Input 20 = momentScalarGrow2622K04P170Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P170_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P170] using h

theorem momentScalarGrow2622K04P170_radius_le :
    (momentScalarGrow2622K04P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P170Expected]

end ConnesWeilRH.Dev
