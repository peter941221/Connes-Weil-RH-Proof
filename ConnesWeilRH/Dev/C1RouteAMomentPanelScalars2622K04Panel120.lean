import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P120 : ℚ := ((-104209451386909523657194994983804133012062155625452329 : ℚ) / 3451941269578634568327570445710548936855310984806400)

def momentPanelGrowth2622K04P120 : ℚ := ((1252994271219249901045972146832554765968052042374831189 : ℚ) / 3887038727773431332240105664297406143828186761055436800)

theorem momentPanelPhase_owner2622K04P120 :
    (momentPanelPhase2622K04P120 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (61 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P120, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P120 :
    (momentPanelGrowth2622K04P120 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P120, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P120Input : RatPair2542 := (momentPanelPhase2622K04P120 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P120Expected : RatState2542 :=
  ((((10344605725576685866984614995402262259385869285891167779159598323528723881930873159 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((209819571165014345467275528633350433 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P120_replay :
    compactExp2620 momentScalarAmp2622K04P120Input 20 = momentScalarAmp2622K04P120Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P120_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (61 / 200) 0) -
      (momentScalarAmp2622K04P120Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P120]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P120 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P120 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P120Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P120_replay] at h
  simpa only [momentPanelPhase_owner2622K04P120] using h

theorem momentScalarAmp2622K04P120_radius_le :
    (momentScalarAmp2622K04P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P120Expected]

def momentScalarGrow2622K04P120Input : RatPair2542 := (momentPanelGrowth2622K04P120 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P120Expected : RatState2542 :=
  ((((2948453334263882664794008420618482799647058585642047832938384985124254771257281541365823844687065 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1868803744956931417172909429204422185468409992557 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P120_replay :
    compactExp2620 momentScalarGrow2622K04P120Input 20 = momentScalarGrow2622K04P120Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P120_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P120Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P120Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P120 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P120]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P120 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P120 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P120Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P120Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P120_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P120] using h

theorem momentScalarGrow2622K04P120_radius_le :
    (momentScalarGrow2622K04P120Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P120Expected]

end ConnesWeilRH.Dev
