import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P113 : ℚ := ((-28505616723208574887811434464000281715129850971723893 : ℚ) / 898951959250848831084561417857764511650672961126400)

def momentPanelGrowth2622K01P113 : ℚ := ((2030116927413247578143236577255065415988013225745433 : ℚ) / 12378554920031107697415540670184707555225971038617600)

theorem momentPanelPhase_owner2622K01P113 :
    (momentPanelPhase2622K01P113 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (47 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P113, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P113 :
    (momentPanelGrowth2622K01P113 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P113, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P113Input : RatPair2542 := (momentPanelPhase2622K01P113 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P113Expected : RatState2542 :=
  ((((36157051851893921477511515323679895837406356031075490852677436914980190892884869275 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11458973645142725304586493708987773 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K01P113_replay :
    compactExp2620 momentScalarAmp2622K01P113Input 20 = momentScalarAmp2622K01P113Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P113_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (47 / 200) 0) -
      (momentScalarAmp2622K01P113Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P113]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P113 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P113 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P113Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P113_replay] at h
  simpa only [momentPanelPhase_owner2622K01P113] using h

theorem momentScalarAmp2622K01P113_radius_le :
    (momentScalarAmp2622K01P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P113Expected]

def momentScalarGrow2622K01P113Input : RatPair2542 := (momentPanelGrowth2622K01P113 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P113Expected : RatState2542 :=
  ((((2516657398874720999350503988695982142669997338219025432739069893680949575870725754776916019818337 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1595120881640955375481539858200618674947397432927 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P113_replay :
    compactExp2620 momentScalarGrow2622K01P113Input 20 = momentScalarGrow2622K01P113Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P113_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P113Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P113Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P113 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P113]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P113 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P113 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P113Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P113Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P113_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P113] using h

theorem momentScalarGrow2622K01P113_radius_le :
    (momentScalarGrow2622K01P113Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P113Expected]

end ConnesWeilRH.Dev
