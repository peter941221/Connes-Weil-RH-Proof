import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P156 : ℚ := ((-108408068886865780161860851818771791107084859088769841 : ℚ) / 2122888218130844727086094550959179065855697328537600)

def momentPanelGrowth2622K02P156 : ℚ := ((1971586046520541398664513221263599657922333552758536053 : ℚ) / 1444903745738117498958893707691764005866396667661516800)

theorem momentPanelPhase_owner2622K02P156 :
    (momentPanelPhase2622K02P156 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (133 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P156, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P156 :
    (momentPanelGrowth2622K02P156 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P156, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P156Input : RatPair2542 := (momentPanelPhase2622K02P156 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P156Expected : RatState2542 :=
  ((((141834458398346831874217578523409656510480491610501363783981493467638612413 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((182223144378564562306239145 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P156_replay :
    compactExp2620 momentScalarAmp2622K02P156Input 20 = momentScalarAmp2622K02P156Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P156_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (133 / 200) 0) -
      (momentScalarAmp2622K02P156Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P156]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P156 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P156 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P156Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P156_replay] at h
  simpa only [momentPanelPhase_owner2622K02P156] using h

theorem momentScalarAmp2622K02P156_radius_le :
    (momentScalarAmp2622K02P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P156Expected]

def momentScalarGrow2622K02P156Input : RatPair2542 := (momentPanelGrowth2622K02P156 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P156Expected : RatState2542 :=
  ((((1044979859596373177582377647969252765697418453087679907033774463197265871956942997332652307094795 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((10597340979637880298442786474850947464420740949845 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P156_replay :
    compactExp2620 momentScalarGrow2622K02P156Input 20 = momentScalarGrow2622K02P156Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P156_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P156Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P156Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P156 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P156]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P156 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P156 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P156Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P156Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P156_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P156] using h

theorem momentScalarGrow2622K02P156_radius_le :
    (momentScalarGrow2622K02P156Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P156Expected]

end ConnesWeilRH.Dev
