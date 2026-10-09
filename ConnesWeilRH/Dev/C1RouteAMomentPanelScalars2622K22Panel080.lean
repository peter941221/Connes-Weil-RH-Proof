import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K22
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K22P080 : ℚ := ((-815239503558136711429399639121474791343 : ℚ) / 26799147809304952131161503124212940800)

def momentPanelGrowth2622K22P080 : ℚ := ((254137878392937395338835671763820523 : ℚ) / 3313131608756500363751783497570713600)

theorem momentPanelPhase_owner2622K22P080 :
    (momentPanelPhase2622K22P080 : ℝ) = momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K22P080 :
    (momentPanelGrowth2622K22P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K22P080Input : RatPair2542 := (momentPanelPhase2622K22P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K22P080Expected : RatState2542 :=
  ((((131282760524152413067963925900243194461604440127963627632730367721571474192782006589 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((166425498298578897385616052568886659 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K22P080_replay :
    compactExp2620 momentScalarAmp2622K22P080Input 20 = momentScalarAmp2622K22P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K22P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K22P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K22P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K22P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K22P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K22P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K22P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K22P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K22P080_replay] at h
  simpa only [momentPanelPhase_owner2622K22P080] using h

theorem momentScalarAmp2622K22P080_radius_le :
    (momentScalarAmp2622K22P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarAmp2622K22P080Expected]

def momentScalarGrow2622K22P080Input : RatPair2542 := (momentPanelGrowth2622K22P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K22P080Expected : RatState2542 :=
  ((((288284786074839955653014131610935815675440332897336203943616606618345210783842353446217368209109 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((730888710742336618779380198713860601194506550731 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K22P080_replay :
    compactExp2620 momentScalarGrow2622K22P080Input 20 = momentScalarGrow2622K22P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K22P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K22P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K22P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K22P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K22P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K22P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K22P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K22P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K22P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K22P080] using h

theorem momentScalarGrow2622K22P080_radius_le :
    (momentScalarGrow2622K22P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarGrow2622K22P080Expected]

end ConnesWeilRH.Dev
