import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P010 : ℚ := ((-374171147987247663762269486663008761834632587770487167 : ℚ) / 4201531757787804697859382236865423782483529511731200)

def momentPanelGrowth2622K04P010 : ℚ := ((14637408039894576103152376037709624943124871060229 : ℚ) / 3853568770306091678857372117513636868233415884800)

theorem momentPanelPhase_owner2622K04P010 :
    (momentPanelPhase2622K04P010 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-159 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P010, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P010 :
    (momentPanelGrowth2622K04P010 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-159 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P010, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P010Input : RatPair2542 := (momentPanelPhase2622K04P010 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P010Expected : RatState2542 :=
  ((((4499012688741040625723550111261475597236872495222760094501 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604462909807316013323703 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P010_replay :
    compactExp2620 momentScalarAmp2622K04P010Input 20 = momentScalarAmp2622K04P010Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P010_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-159 / 200) 0) -
      (momentScalarAmp2622K04P010Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P010]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P010 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P010 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P010Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P010_replay] at h
  simpa only [momentPanelPhase_owner2622K04P010] using h

theorem momentScalarAmp2622K04P010_radius_le :
    (momentScalarAmp2622K04P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P010Expected]

def momentScalarGrow2622K04P010Input : RatPair2542 := (momentPanelGrowth2622K04P010 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P010Expected : RatState2542 :=
  ((((95328810189150707194841972002508428925183473901923868518649284241524118975833346989196044170977957 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((120843185707385958931920200358358082650012336336021 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P010_replay :
    compactExp2620 momentScalarGrow2622K04P010Input 20 = momentScalarGrow2622K04P010Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P010_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-159 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P010Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P010Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P010 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P010]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P010 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P010 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P010Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P010Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P010_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P010] using h

theorem momentScalarGrow2622K04P010_radius_le :
    (momentScalarGrow2622K04P010Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P010Expected]

end ConnesWeilRH.Dev
