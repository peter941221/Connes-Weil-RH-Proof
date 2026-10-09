import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P118 : ℚ := ((-2403909807599740982061150190148720775177 : ℚ) / 74539883534380253975048543201237401600)

def momentPanelGrowth2622K05P118 : ℚ := ((6282076577835717405567381804338175863003 : ℚ) / 28357269896310438382884203296793926041600)

theorem momentPanelPhase_owner2622K05P118 :
    (momentPanelPhase2622K05P118 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (57 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P118, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P118 :
    (momentPanelGrowth2622K05P118 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P118, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P118Input : RatPair2542 := (momentPanelPhase2622K05P118 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P118Expected : RatState2542 :=
  ((((21067351432654698402453384578804967695560269886041270342598588928430508678470478275 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((26706862074281404264764468844973855 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P118_replay :
    compactExp2620 momentScalarAmp2622K05P118Input 20 = momentScalarAmp2622K05P118Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P118_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (57 / 200) 0) -
      (momentScalarAmp2622K05P118Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P118]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P118 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P118 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P118Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P118_replay] at h
  simpa only [momentPanelPhase_owner2622K05P118] using h

theorem momentScalarAmp2622K05P118_radius_le :
    (momentScalarAmp2622K05P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P118Expected]

def momentScalarGrow2622K05P118Input : RatPair2542 := (momentPanelGrowth2622K05P118 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P118Expected : RatState2542 :=
  ((((1332843813755178500988954125853194648168050773957417294633153332763454780068563919165361725259769 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((844789951779388080848874772815099211143721933443 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P118_replay :
    compactExp2620 momentScalarGrow2622K05P118Input 20 = momentScalarGrow2622K05P118Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P118_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P118Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P118]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P118 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P118 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P118Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P118_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P118] using h

theorem momentScalarGrow2622K05P118_radius_le :
    (momentScalarGrow2622K05P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P118Expected]

end ConnesWeilRH.Dev
