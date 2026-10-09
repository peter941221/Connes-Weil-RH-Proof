import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P008 : ℚ := ((-821740046438206682742855089449084838839 : ℚ) / 9080434779554852848801184400749363200)

def momentPanelGrowth2622K05P008 : ℚ := ((1042673305713834165390649577500810666243 : ℚ) / 226744155802583301753954703664322969600)

theorem momentPanelPhase_owner2622K05P008 :
    (momentPanelPhase2622K05P008 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-163 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P008, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P008 :
    (momentPanelGrowth2622K05P008 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P008, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P008Input : RatPair2542 := (momentPanelPhase2622K05P008 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P008Expected : RatState2542 :=
  ((((1066172985091327579247232854811065726756984704630475976697 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229259701171861 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P008_replay :
    compactExp2620 momentScalarAmp2622K05P008Input 20 = momentScalarAmp2622K05P008Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P008_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-163 / 200) 0) -
      (momentScalarAmp2622K05P008Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P008]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P008 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P008 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P008Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P008_replay] at h
  simpa only [momentPanelPhase_owner2622K05P008] using h

theorem momentScalarAmp2622K05P008_radius_le :
    (momentScalarAmp2622K05P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P008Expected]

def momentScalarGrow2622K05P008Input : RatPair2542 := (momentPanelGrowth2622K05P008 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P008Expected : RatState2542 :=
  ((((212169629830504616283266323195176817247926877520000141973573599533358979281685694252608398568425149 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((67238944778839716487681530317601054264738664149483 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P008_replay :
    compactExp2620 momentScalarGrow2622K05P008Input 20 = momentScalarGrow2622K05P008Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P008_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P008Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P008]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P008 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P008 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P008Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P008_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P008] using h

theorem momentScalarGrow2622K05P008_radius_le :
    (momentScalarGrow2622K05P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P008Expected]

end ConnesWeilRH.Dev
