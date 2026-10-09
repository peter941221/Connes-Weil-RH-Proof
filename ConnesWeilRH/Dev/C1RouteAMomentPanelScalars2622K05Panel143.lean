import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P143 : ℚ := ((-796722947807275125016008762426001390609 : ℚ) / 19302769219795294742470599048901427200)

def momentPanelGrowth2622K05P143 : ℚ := ((2098480420765446679506416571289272324249 : ℚ) / 3180729052984342441807777038538165452800)

theorem momentPanelPhase_owner2622K05P143 :
    (momentPanelPhase2622K05P143 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (107 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P143 :
    (momentPanelGrowth2622K05P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P143Input : RatPair2542 := (momentPanelPhase2622K05P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P143Expected : RatState2542 :=
  ((((2535525818065389374471720593982799116619812212908189667778963289408767673463641 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3214289764403823307099403575157 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P143_replay :
    compactExp2620 momentScalarAmp2622K05P143Input 20 = momentScalarAmp2622K05P143Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622K05P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P143]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P143 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P143_replay] at h
  simpa only [momentPanelPhase_owner2622K05P143] using h

theorem momentScalarAmp2622K05P143_radius_le :
    (momentScalarAmp2622K05P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P143Expected]

def momentScalarGrow2622K05P143Input : RatPair2542 := (momentPanelGrowth2622K05P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P143Expected : RatState2542 :=
  ((((4131651062027370030467034876619579083080309976527493001679650474751969052295567537334344690852059 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2618743326681865990898447336511848303916120046035 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P143_replay :
    compactExp2620 momentScalarGrow2622K05P143Input 20 = momentScalarGrow2622K05P143Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P143_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P143] using h

theorem momentScalarGrow2622K05P143_radius_le :
    (momentScalarGrow2622K05P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P143Expected]

end ConnesWeilRH.Dev
