import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P009 : ℚ := ((-118588756123041285528879404141002505129240356677055067 : ℚ) / 1339614684373813944361307210925296135008845981286400)

def momentPanelGrowth2622K02P009 : ℚ := ((7005435399779708176335805706150724221155662378205160559 : ℚ) / 1687966025952712255046953289889370256885569353573990400)

theorem momentPanelPhase_owner2622K02P009 :
    (momentPanelPhase2622K02P009 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-161 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P009, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P009 :
    (momentPanelGrowth2622K02P009 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P009, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P009Input : RatPair2542 := (momentPanelPhase2622K02P009 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P009Expected : RatState2542 :=
  ((((3826970229738271652808824624342237755048535834602448597537 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((604462909807317013260799 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P009_replay :
    compactExp2620 momentScalarAmp2622K02P009Input 20 = momentScalarAmp2622K02P009Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P009_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-161 / 200) 0) -
      (momentScalarAmp2622K02P009Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P009]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P009 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P009 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P009Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P009_replay] at h
  simpa only [momentPanelPhase_owner2622K02P009] using h

theorem momentScalarAmp2622K02P009_radius_le :
    (momentScalarAmp2622K02P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P009Expected]

def momentScalarGrow2622K02P009Input : RatPair2542 := (momentPanelGrowth2622K02P009 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P009Expected : RatState2542 :=
  ((((135524418894894101936260462628918911608313306798397598294632132832687689586517559417790728694842785 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((85898465495392140512700611000282831430461239275509 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P009_replay :
    compactExp2620 momentScalarGrow2622K02P009Input 20 = momentScalarGrow2622K02P009Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P009_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P009Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P009Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P009 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P009]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P009 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P009 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P009Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P009Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P009_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P009] using h

theorem momentScalarGrow2622K02P009_radius_le :
    (momentScalarGrow2622K02P009Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P009Expected]

end ConnesWeilRH.Dev
