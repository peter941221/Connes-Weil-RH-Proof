import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P133 : ℚ := ((-304404185506076670489062238081539134214566974646605081 : ℚ) / 9257413984429396980520254455043315353605771152588800)

def momentPanelGrowth2622K04P133 : ℚ := ((94540436148862904384935332379747748062380516191221 : ℚ) / 188824869744998492264011233758168206543437378355200)

theorem momentPanelPhase_owner2622K04P133 :
    (momentPanelPhase2622K04P133 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (87 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P133, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P133 :
    (momentPanelGrowth2622K04P133 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P133, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P133Input : RatPair2542 := (momentPanelPhase2622K04P133 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P133Expected : RatState2542 :=
  ((((11195368072669400308482265285689669261194978442347722169955582387421379173222994383 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((14192260106406044688791759550945451 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P133_replay :
    compactExp2620 momentScalarAmp2622K04P133Input 20 = momentScalarAmp2622K04P133Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P133_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (87 / 200) 0) -
      (momentScalarAmp2622K04P133Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P133]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P133 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P133 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P133Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P133_replay] at h
  simpa only [momentPanelPhase_owner2622K04P133] using h

theorem momentScalarAmp2622K04P133_radius_le :
    (momentScalarAmp2622K04P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P133Expected]

def momentScalarGrow2622K04P133Input : RatPair2542 := (momentPanelGrowth2622K04P133 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P133Expected : RatState2542 :=
  ((((440504417024814201027073938087219923059543912849384683096556653902491869825421690890700891640839 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((4467243376121406178641714161506307275852788139757 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P133_replay :
    compactExp2620 momentScalarGrow2622K04P133Input 20 = momentScalarGrow2622K04P133Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P133_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P133Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P133]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P133 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P133 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P133Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P133_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P133] using h

theorem momentScalarGrow2622K04P133_radius_le :
    (momentScalarGrow2622K04P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P133Expected]

end ConnesWeilRH.Dev
