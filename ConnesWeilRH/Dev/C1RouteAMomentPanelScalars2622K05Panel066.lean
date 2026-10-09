import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P066 : ℚ := ((-819769499294962860672500398584038012251 : ℚ) / 25549751377720009233046352444994355200)

def momentPanelGrowth2622K05P066 : ℚ := ((62009156491150040091358265611301736969 : ℚ) / 351819691105422057757310218169797836800)

theorem momentPanelPhase_owner2622K05P066 :
    (momentPanelPhase2622K05P066 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-47 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P066, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P066 :
    (momentPanelGrowth2622K05P066 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-47 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P066, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P066Input : RatPair2542 := (momentPanelPhase2622K05P066 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P066Expected : RatState2542 :=
  ((((3105080310281179031933756726427639487932703093613894987372301524928678196712909593 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((3936277363121349138859221677148811 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K05P066_replay :
    compactExp2620 momentScalarAmp2622K05P066Input 20 = momentScalarAmp2622K05P066Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P066_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-47 / 200) 0) -
      (momentScalarAmp2622K05P066Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P066]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P066 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P066 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P066Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P066_replay] at h
  simpa only [momentPanelPhase_owner2622K05P066] using h

theorem momentScalarAmp2622K05P066_radius_le :
    (momentScalarAmp2622K05P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P066Expected]

def momentScalarGrow2622K05P066Input : RatPair2542 := (momentPanelGrowth2622K05P066 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P066Expected : RatState2542 :=
  ((((2547675849561913878918774092977318019560358917966947657553716765166286572237450837658927216233811 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3229562277034592657374303306004157894433726917679 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P066_replay :
    compactExp2620 momentScalarGrow2622K05P066Input 20 = momentScalarGrow2622K05P066Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P066_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-47 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P066Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P066Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P066 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P066]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P066 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P066 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P066Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P066Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P066_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P066] using h

theorem momentScalarGrow2622K05P066_radius_le :
    (momentScalarGrow2622K05P066Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P066Expected]

end ConnesWeilRH.Dev
