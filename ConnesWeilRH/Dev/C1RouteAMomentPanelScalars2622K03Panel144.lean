import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P144 : ℚ := ((-72798818628493823466683731435981483543962463361179775 : ℚ) / 1712331855837819131540392242131215092904381965664256)

def momentPanelGrowth2622K03P144 : ℚ := ((1614668052347660491158042255676141541779005311237075 : ℚ) / 2370098936489058626164438147155587219438280105787392)

theorem momentPanelPhase_owner2622K03P144 :
    (momentPanelPhase2622K03P144 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (109 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P144, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P144 :
    (momentPanelGrowth2622K03P144 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P144, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P144Input : RatPair2542 := (momentPanelPhase2622K03P144 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P144Expected : RatState2542 :=
  ((((734200691951302220506454674719340515278466973452191833420206704637169120797945 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((465375051010026498496016833473 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P144_replay :
    compactExp2620 momentScalarAmp2622K03P144Input 20 = momentScalarAmp2622K03P144Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P144_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (109 / 200) 0) -
      (momentScalarAmp2622K03P144Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P144]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P144 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P144 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P144Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P144_replay] at h
  simpa only [momentPanelPhase_owner2622K03P144] using h

theorem momentScalarAmp2622K03P144_radius_le :
    (momentScalarAmp2622K03P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P144Expected]

def momentScalarGrow2622K03P144Input : RatPair2542 := (momentPanelGrowth2622K03P144 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P144Expected : RatState2542 :=
  ((((4221518717276826731759786034240067417017432157701473370454823638388871548944012771854298123425741 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5351407258988250191352852931747117926130875619215 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P144_replay :
    compactExp2620 momentScalarGrow2622K03P144Input 20 = momentScalarGrow2622K03P144Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P144_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P144Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P144]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P144 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P144 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P144Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P144_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P144] using h

theorem momentScalarGrow2622K03P144_radius_le :
    (momentScalarGrow2622K03P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P144Expected]

end ConnesWeilRH.Dev
