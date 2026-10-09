import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P154 : ℚ := ((-85434653459311410811933828056954659204952528587090097 : ℚ) / 1666953942695925843082025098018537844538228919500800)

def momentPanelGrowth2622K01P154 : ℚ := ((743350590446766547239897184249653636283938878027851 : ℚ) / 634661367754022710109593313464954249770997855027200)

theorem momentPanelPhase_owner2622K01P154 :
    (momentPanelPhase2622K01P154 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (129 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P154, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P154 :
    (momentPanelGrowth2622K01P154 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P154, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P154Input : RatPair2542 := (momentPanelPhase2622K01P154 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P154Expected : RatState2542 :=
  ((((117802922913246214198306731191162997975277833993274475609648109848103814713 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((151758096804614020180831343 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P154_replay :
    compactExp2620 momentScalarAmp2622K01P154Input 20 = momentScalarAmp2622K01P154Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P154_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (129 / 200) 0) -
      (momentScalarAmp2622K01P154Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P154]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P154 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P154 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P154Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P154_replay] at h
  simpa only [momentPanelPhase_owner2622K01P154] using h

theorem momentScalarAmp2622K01P154_radius_le :
    (momentScalarAmp2622K01P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P154Expected]

def momentScalarGrow2622K01P154Input : RatPair2542 := (momentPanelGrowth2622K01P154 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P154Expected : RatState2542 :=
  ((((6890780156933740815988736455942461945257752025877720173975645133083236185054222928228731452355975 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8735091844907568140945449025175725119129048578303 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P154_replay :
    compactExp2620 momentScalarGrow2622K01P154Input 20 = momentScalarGrow2622K01P154Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P154_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P154Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P154]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P154 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P154 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P154Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P154_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P154] using h

theorem momentScalarGrow2622K01P154_radius_le :
    (momentScalarGrow2622K01P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P154Expected]

end ConnesWeilRH.Dev
