import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P147 : ℚ := ((-14161401633421140243871927577171453176318924445736619 : ℚ) / 326097552829457713624197178299820648760729948651520)

def momentPanelGrowth2622P147 : ℚ := ((1706290359706387129653215030967739902662406538543400117 : ℚ) / 2095032910361841049279456195350627159177942539226316800)

theorem momentPanelPhase_owner2622P147 :
    (momentPanelPhase2622P147 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (23 / 40) 0 := by
  norm_num [momentPanelPhase2622P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P147 :
    (momentPanelGrowth2622P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P147Input : RatPair2542 := (momentPanelPhase2622P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P147Expected : RatState2542 :=
  ((((147404639258879545378536214910797193454186278994659337960289877818806926253841 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((186866527245651186894673279017 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P147_replay :
    compactExp2620 momentScalarAmp2622P147Input 20 = momentScalarAmp2622P147Expected := by
  decide +kernel

theorem momentScalarAmp2622P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P147]
  have h := compactExp_real_error2620 momentPanelPhase2622P147 20 hsmall
  change |Real.exp (momentPanelPhase2622P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P147_replay] at h
  simpa only [momentPanelPhase_owner2622P147] using h

theorem momentScalarAmp2622P147_radius_le :
    (momentScalarAmp2622P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarAmp2622P147Expected]

def momentScalarGrow2622P147Input : RatPair2542 := (momentPanelGrowth2622P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P147Expected : RatState2542 :=
  ((((602861931093536364965607014972664926829802910776894246307784346409682265114190828532152528085299 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((6113741561801876975012599124281808161551831356015 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P147_replay :
    compactExp2620 momentScalarGrow2622P147Input 20 = momentScalarGrow2622P147Expected := by
  decide +kernel

theorem momentScalarGrow2622P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P147_replay] at h
  simpa only [momentPanelGrowth_owner2622P147] using h

theorem momentScalarGrow2622P147_radius_le :
    (momentScalarGrow2622P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P147Expected]

end ConnesWeilRH.Dev
