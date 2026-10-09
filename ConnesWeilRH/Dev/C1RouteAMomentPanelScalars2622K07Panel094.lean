import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P094 : ℚ := ((-96178938754927041581702056498147728675 : ℚ) / 3238614035872684126614201296345890816)

def momentPanelGrowth2622K07P094 : ℚ := ((238700324401605871768000702318133225 : ℚ) / 2152653260873966388775217567990022144)

theorem momentPanelPhase_owner2622K07P094 :
    (momentPanelPhase2622K07P094 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (9 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P094 :
    (momentPanelGrowth2622K07P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P094Input : RatPair2542 := (momentPanelPhase2622K07P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P094Expected : RatState2542 :=
  ((((270465345762652971286891962808163085541354923069686232018104432375731017307721079945 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((85716317080980524198860865472510029 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P094_replay :
    compactExp2620 momentScalarAmp2622K07P094Input 20 = momentScalarAmp2622K07P094Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622K07P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P094]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P094 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P094_replay] at h
  simpa only [momentPanelPhase_owner2622K07P094] using h

theorem momentScalarAmp2622K07P094_radius_le :
    (momentScalarAmp2622K07P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P094Expected]

def momentScalarGrow2622K07P094Input : RatPair2542 := (momentPanelGrowth2622K07P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P094Expected : RatState2542 :=
  ((((2386470308953460285855099353104935002981827170388830384643189478456752855367304628731022419643631 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1512605099828354712552226320521611599615503006029 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P094_replay :
    compactExp2620 momentScalarGrow2622K07P094Input 20 = momentScalarGrow2622K07P094Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P094_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P094] using h

theorem momentScalarGrow2622K07P094_radius_le :
    (momentScalarGrow2622K07P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P094Expected]

end ConnesWeilRH.Dev
