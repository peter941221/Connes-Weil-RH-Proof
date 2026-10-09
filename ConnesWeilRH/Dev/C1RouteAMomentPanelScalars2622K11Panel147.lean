import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K11
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K11P147 : ℚ := ((-6361403375914610356104849552095075141 : ℚ) / 144816404570072926826983374182154240)

def momentPanelGrowth2622K11P147 : ℚ := ((749647096955729026352390107291789385563 : ℚ) / 930381509772467052101532745278790041600)

theorem momentPanelPhase_owner2622K11P147 :
    (momentPanelPhase2622K11P147 : ℝ) = momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (23 / 40) 0 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P147, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K11P147 :
    (momentPanelGrowth2622K11P147 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2))
      (23 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P147, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K11P147Input : RatPair2542 := (momentPanelPhase2622K11P147 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K11P147Expected : RatState2542 :=
  ((((178725057568727630998151298377050631049989311806677767968665942386533774294605 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((113286417867324229803232308267 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K11P147_replay :
    compactExp2620 momentScalarAmp2622K11P147Input 20 = momentScalarAmp2622K11P147Expected := by
  decide +kernel

theorem momentScalarAmp2622K11P147_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (23 / 40) 0) -
      (momentScalarAmp2622K11P147Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K11P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K11P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelPhase2622K11P147]
  have h := compactExp_real_error2620 momentPanelPhase2622K11P147 20 hsmall
  change |Real.exp (momentPanelPhase2622K11P147 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K11P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K11P147Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K11P147_replay] at h
  simpa only [momentPanelPhase_owner2622K11P147] using h

theorem momentScalarAmp2622K11P147_radius_le :
    (momentScalarAmp2622K11P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarAmp2622K11P147Expected]

def momentScalarGrow2622K11P147Input : RatPair2542 := (momentPanelGrowth2622K11P147 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K11P147Expected : RatState2542 :=
  ((((4781099128221750227210294016663611400764403704920969680794535204224401123067667880757546392839321 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1515189630615232203337614859885131052097250798213 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K11P147_replay :
    compactExp2620 momentScalarGrow2622K11P147Input 20 = momentScalarGrow2622K11P147Expected := by
  decide +kernel

theorem momentScalarGrow2622K11P147_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 11).re * (storedWidth 11 ^ 2)) (23 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K11P147Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K11P147Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K11P147 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentPanelGrowth2622K11P147]
  have h := compactExp_real_error2620 momentPanelGrowth2622K11P147 20 hsmall
  change |Real.exp (momentPanelGrowth2622K11P147 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K11P147Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K11P147Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K11P147_replay] at h
  simpa only [momentPanelGrowth_owner2622K11P147] using h

theorem momentScalarGrow2622K11P147_radius_le :
    (momentScalarGrow2622K11P147Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, momentScalarGrow2622K11P147Expected]

end ConnesWeilRH.Dev
