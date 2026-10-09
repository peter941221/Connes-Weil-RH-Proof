import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P023 : ℚ := ((-73342547141372766243268308156543405370293690174624425 : ℚ) / 1358648459603740625335100512613874602147646290264064)

def momentPanelGrowth2622K03P023 : ℚ := ((1226745142836844607480271435562075879211190884318791475 : ℚ) / 924738397272395199333691972922728963754493867303370752)

theorem momentPanelPhase_owner2622K03P023 :
    (momentPanelPhase2622K03P023 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-133 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P023, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P023 :
    (momentPanelGrowth2622K03P023 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P023, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P023Input : RatPair2542 := (momentPanelPhase2622K03P023 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P023Expected : RatState2542 :=
  ((((7682779468271217839182168443644595024420635213358482712412388051271673445 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6078716518203310008835315 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P023_replay :
    compactExp2620 momentScalarAmp2622K03P023Input 20 = momentScalarAmp2622K03P023Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P023_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-133 / 200) 0) -
      (momentScalarAmp2622K03P023Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P023]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P023 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P023 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P023Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P023_replay] at h
  simpa only [momentPanelPhase_owner2622K03P023] using h

theorem momentScalarAmp2622K03P023_radius_le :
    (momentScalarAmp2622K03P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P023Expected]

def momentScalarGrow2622K03P023Input : RatPair2542 := (momentPanelGrowth2622K03P023 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P023Expected : RatState2542 :=
  ((((1006091932922990904475395138894209791668214011647700259382855650783378237982333132370388593480761 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2550742858282976442937178202870805954454262080377 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K03P023_replay :
    compactExp2620 momentScalarGrow2622K03P023Input 20 = momentScalarGrow2622K03P023Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P023_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P023Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P023]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P023 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P023 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P023Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P023_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P023] using h

theorem momentScalarGrow2622K03P023_radius_le :
    (momentScalarGrow2622K03P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P023Expected]

end ConnesWeilRH.Dev
