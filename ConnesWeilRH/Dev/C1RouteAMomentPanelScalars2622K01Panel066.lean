import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P066 : ℚ := ((-28584290985029820354520004313979523740180013988276107 : ℚ) / 898951959250848831084561417857764511650672961126400)

def momentPanelGrowth2622K01P066 : ℚ := ((2030116927413247578143236577255065415988013225745433 : ℚ) / 12378554920031107697415540670184707555225971038617600)

theorem momentPanelPhase_owner2622K01P066 :
    (momentPanelPhase2622K01P066 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-47 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P066, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P066 :
    (momentPanelGrowth2622K01P066 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P066, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P066Input : RatPair2542 := (momentPanelPhase2622K01P066 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P066Expected : RatState2542 :=
  ((((2070449056621007413089132492384699892255461950991488141888381789434107928754420549 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((20997484640875553254482441775535481 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P066_replay :
    compactExp2620 momentScalarAmp2622K01P066Input 20 = momentScalarAmp2622K01P066Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P066_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-47 / 200) 0) -
      (momentScalarAmp2622K01P066Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P066]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P066 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P066 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P066Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P066_replay] at h
  simpa only [momentPanelPhase_owner2622K01P066] using h

theorem momentScalarAmp2622K01P066_radius_le :
    (momentScalarAmp2622K01P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P066Expected]

def momentScalarGrow2622K01P066Input : RatPair2542 := (momentPanelGrowth2622K01P066 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P066Expected : RatState2542 :=
  ((((2516657398874720999350503988695982142669997338219025432739069893680949575870725754776916019818337 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1595120881640955375481539858200618674947397432927 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P066_replay :
    compactExp2620 momentScalarGrow2622K01P066Input 20 = momentScalarGrow2622K01P066Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P066_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P066Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P066]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P066 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P066 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P066Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P066_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P066] using h

theorem momentScalarGrow2622K01P066_radius_le :
    (momentScalarGrow2622K01P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P066Expected]

end ConnesWeilRH.Dev
