import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K18
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K18P066 : ℚ := ((-820595676055512815718709718565630004771 : ℚ) / 25549751377720009233046352444994355200)

def momentPanelGrowth2622K18P066 : ℚ := ((62493260386111101327799200547404178849 : ℚ) / 351819691105422057757310218169797836800)

theorem momentPanelPhase_owner2622K18P066 :
    (momentPanelPhase2622K18P066 : ℝ) = momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-47 / 200) 0 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P066, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K18P066 :
    (momentPanelGrowth2622K18P066 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2))
      (-47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P066, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K18P066Input : RatPair2542 := (momentPanelPhase2622K18P066 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K18P066Expected : RatState2542 :=
  ((((24050243507575957725582575524977517532094197854696321654968134242533121674645035053 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7622059862879998315675468924543605 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K18P066_replay :
    compactExp2620 momentScalarAmp2622K18P066Input 20 = momentScalarAmp2622K18P066Expected := by
  decide +kernel

theorem momentScalarAmp2622K18P066_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-47 / 200) 0) -
      (momentScalarAmp2622K18P066Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K18P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K18P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P066]
  have h := compactExp_real_error2620 momentPanelPhase2622K18P066 20 hsmall
  change |Real.exp (momentPanelPhase2622K18P066 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K18P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K18P066Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K18P066_replay] at h
  simpa only [momentPanelPhase_owner2622K18P066] using h

theorem momentScalarAmp2622K18P066_radius_le :
    (momentScalarAmp2622K18P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarAmp2622K18P066Expected]

def momentScalarGrow2622K18P066Input : RatPair2542 := (momentPanelGrowth2622K18P066 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K18P066Expected : RatState2542 :=
  ((((318897983061460437740642707020105069675752420036413402091586328886429490284748507821668287079805 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1617004604637301036225264646453130324741510626171 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K18P066_replay :
    compactExp2620 momentScalarGrow2622K18P066Input 20 = momentScalarGrow2622K18P066Expected := by
  decide +kernel

theorem momentScalarGrow2622K18P066_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K18P066Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K18P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K18P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P066]
  have h := compactExp_real_error2620 momentPanelGrowth2622K18P066 20 hsmall
  change |Real.exp (momentPanelGrowth2622K18P066 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K18P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K18P066Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K18P066_replay] at h
  simpa only [momentPanelGrowth_owner2622K18P066] using h

theorem momentScalarGrow2622K18P066_radius_le :
    (momentScalarGrow2622K18P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarGrow2622K18P066Expected]

end ConnesWeilRH.Dev
