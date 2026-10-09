import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P111 : ℚ := ((-803470539036059245954824325324203161041 : ℚ) / 25793140292963829278133719460426547200)

def momentPanelGrowth2622K05P111 : ℚ := ((305882012169935672374255030745436029683 : ℚ) / 1913185949527012394164320753593981337600)

theorem momentPanelPhase_owner2622K05P111 :
    (momentPanelPhase2622K05P111 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (43 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P111, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P111 :
    (momentPanelGrowth2622K05P111 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P111, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P111Input : RatPair2542 := (momentPanelPhase2622K05P111 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P111Expected : RatState2542 :=
  ((((7906715311798623343438420910617723559930336530171702981587550692564371606157489939 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((20046500344450975358344202945190921 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P111_replay :
    compactExp2620 momentScalarAmp2622K05P111Input 20 = momentScalarAmp2622K05P111Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P111_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (43 / 200) 0) -
      (momentScalarAmp2622K05P111Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P111]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P111 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P111 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P111Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P111_replay] at h
  simpa only [momentPanelPhase_owner2622K05P111] using h

theorem momentScalarAmp2622K05P111_radius_le :
    (momentScalarAmp2622K05P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P111Expected]

def momentScalarGrow2622K05P111Input : RatPair2542 := (momentPanelGrowth2622K05P111 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P111Expected : RatState2542 :=
  ((((2506305646299481550314920595043937666677885407347282771865370539369414198065436307923981729194477 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3177119372457632397665460501079115497242204433613 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P111_replay :
    compactExp2620 momentScalarGrow2622K05P111Input 20 = momentScalarGrow2622K05P111Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P111_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P111Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P111]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P111 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P111 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P111Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P111_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P111] using h

theorem momentScalarGrow2622K05P111_radius_le :
    (momentScalarGrow2622K05P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P111Expected]

end ConnesWeilRH.Dev
