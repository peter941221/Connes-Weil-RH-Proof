import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P147 : ℚ := ((-865525466431156056829563225894685707836917787237731 : ℚ) / 20381097051841107101512323643738790547545621790720)

def momentPanelGrowth2622K02P147 : ℚ := ((108828853416371497291085345073161353031090628339911933 : ℚ) / 130939556897615065579966012209414197448621408701644800)

theorem momentPanelPhase_owner2622K02P147 :
    (momentPanelPhase2622K02P147 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (23 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P147 :
    (momentPanelGrowth2622K02P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P147Input : RatPair2542 := (momentPanelPhase2622K02P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P147Expected : RatState2542 :=
  ((((96226490816917184749905224366626149663618072145276850641655202885539972518639 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((487947245587566674246338271421 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P147_replay :
    compactExp2620 momentScalarAmp2622K02P147Input 20 = momentScalarAmp2622K02P147Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622K02P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P147]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P147 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P147_replay] at h
  simpa only [momentPanelPhase_owner2622K02P147] using h

theorem momentScalarAmp2622K02P147_radius_le :
    (momentScalarAmp2622K02P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P147Expected]

def momentScalarGrow2622K02P147Input : RatPair2542 := (momentPanelGrowth2622K02P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P147Expected : RatState2542 :=
  ((((613009651503033391571022891488539386509756332592262269301038737003135173796475653877620655141463 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((6216651493850316107999343167622244052392245873159 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P147_replay :
    compactExp2620 momentScalarGrow2622K02P147Input 20 = momentScalarGrow2622K02P147Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P147_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P147] using h

theorem momentScalarGrow2622K02P147_radius_le :
    (momentScalarGrow2622K02P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P147Expected]

end ConnesWeilRH.Dev
