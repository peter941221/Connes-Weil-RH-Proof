import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P084 : ℚ := ((-28554669090764775153032076634782564190979457558386879 : ℚ) / 948620178957016234945389769594606942396792543641600)

def momentPanelGrowth2622K01P084 : ℚ := ((8440541513847236534305463059530304238890175763583113 : ℚ) / 221404688507589756117925754039941068259024745109913600)

theorem momentPanelPhase_owner2622K01P084 :
    (momentPanelPhase2622K01P084 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P084 :
    (momentPanelGrowth2622K01P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P084Input : RatPair2542 := (momentPanelPhase2622K01P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P084Expected : RatState2542 :=
  ((((180627780943639857087369119237435900692048685706271784395582779927445956846904753633 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((228979488108689234613831264144863499 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P084_replay :
    compactExp2620 momentScalarAmp2622K01P084Input 20 = momentScalarAmp2622K01P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K01P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P084_replay] at h
  simpa only [momentPanelPhase_owner2622K01P084] using h

theorem momentScalarAmp2622K01P084_radius_le :
    (momentScalarAmp2622K01P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P084Expected]

def momentScalarGrow2622K01P084Input : RatPair2542 := (momentPanelGrowth2622K01P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P084Expected : RatState2542 :=
  ((((2218988670330806955406388935929095449768388169650443581925322885897612320935803548457658998978341 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2812902217576849799577774451791280584006108772059 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P084_replay :
    compactExp2620 momentScalarGrow2622K01P084Input 20 = momentScalarGrow2622K01P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P084] using h

theorem momentScalarGrow2622K01P084_radius_le :
    (momentScalarGrow2622K01P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P084Expected]

end ConnesWeilRH.Dev
