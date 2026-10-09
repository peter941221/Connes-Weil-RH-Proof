import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P171 : ℚ := ((-800852721853926951172925013432195161161 : ℚ) / 9080434779554852848801184400749363200)

def momentPanelGrowth2622K05P171 : ℚ := ((1042673305713834165390649577500810666243 : ℚ) / 226744155802583301753954703664322969600)

theorem momentPanelPhase_owner2622K05P171 :
    (momentPanelPhase2622K05P171 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (163 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P171, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P171 :
    (momentPanelGrowth2622K05P171 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P171, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P171Input : RatPair2542 := (momentPanelPhase2622K05P171 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P171Expected : RatState2542 :=
  ((((664807911648775320478115418110281803430047869988144298989 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1208925819614635917397073 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P171_replay :
    compactExp2620 momentScalarAmp2622K05P171Input 20 = momentScalarAmp2622K05P171Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P171_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (163 / 200) 0) -
      (momentScalarAmp2622K05P171Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P171]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P171 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P171 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P171Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P171_replay] at h
  simpa only [momentPanelPhase_owner2622K05P171] using h

theorem momentScalarAmp2622K05P171_radius_le :
    (momentScalarAmp2622K05P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P171Expected]

def momentScalarGrow2622K05P171Input : RatPair2542 := (momentPanelGrowth2622K05P171 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P171Expected : RatState2542 :=
  ((((212169629830504616283266323195176817247926877520000141973573599533358979281685694252608398568425149 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((67238944778839716487681530317601054264738664149483 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P171_replay :
    compactExp2620 momentScalarGrow2622K05P171Input 20 = momentScalarGrow2622K05P171Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P171_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P171Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P171Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P171 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P171]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P171 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P171 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P171Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P171Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P171_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P171] using h

theorem momentScalarGrow2622K05P171_radius_le :
    (momentScalarGrow2622K05P171Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P171Expected]

end ConnesWeilRH.Dev
