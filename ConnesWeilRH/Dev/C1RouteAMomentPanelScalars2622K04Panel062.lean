import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P062 : ℚ := ((-986735613143076614899691432642238917674951407511921 : ℚ) / 28145324500161528854469399317544044089467763425280)

def momentPanelGrowth2622K04P062 : ℚ := ((1127163614737879450727475463861834372958844820229 : ℚ) / 3853568770306091678857372117513636868233415884800)

theorem momentPanelPhase_owner2622K04P062 :
    (momentPanelPhase2622K04P062 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-11 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P062, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P062 :
    (momentPanelGrowth2622K04P062 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-11 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P062, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P062Input : RatPair2542 := (momentPanelPhase2622K04P062 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P062Expected : RatState2542 :=
  ((((1270114929312985763576858354880196081932900979134404450842107810845735460982170223 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((805057893705680909810928207265059 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P062_replay :
    compactExp2620 momentScalarAmp2622K04P062Input 20 = momentScalarAmp2622K04P062Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P062_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-11 / 40) 0) -
      (momentScalarAmp2622K04P062Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P062]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P062 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P062 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P062Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P062_replay] at h
  simpa only [momentPanelPhase_owner2622K04P062] using h

theorem momentScalarAmp2622K04P062_radius_le :
    (momentScalarAmp2622K04P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P062Expected]

def momentScalarGrow2622K04P062Input : RatPair2542 := (momentPanelGrowth2622K04P062 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P062Expected : RatState2542 :=
  ((((357716662150029571023149234857937228298582121424849967126404645902713905569750044035040446662993 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((906919229988509473731389047827053808814335679539 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K04P062_replay :
    compactExp2620 momentScalarGrow2622K04P062Input 20 = momentScalarGrow2622K04P062Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P062_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-11 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P062Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P062Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P062 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P062]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P062 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P062 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P062Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P062Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P062_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P062] using h

theorem momentScalarGrow2622K04P062_radius_le :
    (momentScalarGrow2622K04P062Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P062Expected]

end ConnesWeilRH.Dev
