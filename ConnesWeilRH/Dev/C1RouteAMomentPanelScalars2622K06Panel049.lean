import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P049 : ℚ := ((-62708559 : ℚ) / 1671950)

def momentPanelGrowth2622K06P049 : ℚ := ((228068587 : ℚ) / 576714675)

theorem momentPanelPhase_owner2622K06P049 :
    (momentPanelPhase2622K06P049 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P049 :
    (momentPanelGrowth2622K06P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P049Input : RatPair2542 := (momentPanelPhase2622K06P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P049Expected : RatState2542 :=
  ((((27465359257983384887374256418655733551884961496831751083994856560445531898240565 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((139270900468543889825434273513809 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P049_replay :
    compactExp2620 momentScalarAmp2622K06P049Input 20 = momentScalarAmp2622K06P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K06P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P049_replay] at h
  simpa only [momentPanelPhase_owner2622K06P049] using h

theorem momentScalarAmp2622K06P049_radius_le :
    (momentScalarAmp2622K06P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P049Expected]

def momentScalarGrow2622K06P049Input : RatPair2542 := (momentPanelGrowth2622K06P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P049Expected : RatState2542 :=
  ((((3172089720521297955564201631348398189504586124508672377200772378877664648484791164966363315364053 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2010549960835933803160345732235788831651625515717 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P049_replay :
    compactExp2620 momentScalarGrow2622K06P049Input 20 = momentScalarGrow2622K06P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P049] using h

theorem momentScalarGrow2622K06P049_radius_le :
    (momentScalarGrow2622K06P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P049Expected]

end ConnesWeilRH.Dev
