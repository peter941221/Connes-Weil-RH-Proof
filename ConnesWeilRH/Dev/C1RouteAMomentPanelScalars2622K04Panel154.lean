import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P154 : ℚ := ((-301811633784694139585472267420154712068665033602627103 : ℚ) / 6667815770783703372328100392074151378152915678003200)

def momentPanelGrowth2622K04P154 : ℚ := ((3209083708383794371228419527446038733859925553379749 : ℚ) / 2538645471016090840438373253859816999083991420108800)

theorem momentPanelPhase_owner2622K04P154 :
    (momentPanelPhase2622K04P154 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (129 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P154, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P154 :
    (momentPanelGrowth2622K04P154 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (129 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P154, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P154Input : RatPair2542 := (momentPanelPhase2622K04P154 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P154Expected : RatState2542 :=
  ((((46958896871559296106989069856430080241257484182017227902800748923821811630329 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((59532461338424186974843496315 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P154_replay :
    compactExp2620 momentScalarAmp2622K04P154Input 20 = momentScalarAmp2622K04P154Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P154_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (129 / 200) 0) -
      (momentScalarAmp2622K04P154Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P154]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P154 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P154 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P154Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P154_replay] at h
  simpa only [momentPanelPhase_owner2622K04P154] using h

theorem momentScalarAmp2622K04P154_radius_le :
    (momentScalarAmp2622K04P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P154Expected]

def momentScalarGrow2622K04P154Input : RatPair2542 := (momentPanelGrowth2622K04P154 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P154Expected : RatState2542 :=
  ((((7561138309825921925224927110331490280096095924250545609854475316041037060434219599523096173581353 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2396217490494040027015501575556289041332104269285 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P154_replay :
    compactExp2620 momentScalarGrow2622K04P154Input 20 = momentScalarGrow2622K04P154Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P154_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (129 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P154Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P154Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P154 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P154]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P154 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P154 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P154Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P154Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P154_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P154] using h

theorem momentScalarGrow2622K04P154_radius_le :
    (momentScalarGrow2622K04P154Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P154Expected]

end ConnesWeilRH.Dev
