import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P019 : ℚ := ((-359092698428408870800891597794202029059155695790855941 : ℚ) / 5742959265910241369402331083870878529776895865651200)

def momentPanelGrowth2622K02P019 : ℚ := ((2074524411948225089855286224332840666058253465407496133 : ℚ) / 1169947332233699739792777032249257666832533296041164800)

theorem momentPanelPhase_owner2622K02P019 :
    (momentPanelPhase2622K02P019 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-141 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P019, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P019 :
    (momentPanelGrowth2622K02P019 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-141 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P019, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P019Input : RatPair2542 := (momentPanelPhase2622K02P019 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P019Expected : RatState2542 :=
  ((((1493703992958666951961429987514591675441812393989691791818911034932927 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((604936311726668232983523 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P019_replay :
    compactExp2620 momentScalarAmp2622K02P019Input 20 = momentScalarAmp2622K02P019Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P019_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-141 / 200) 0) -
      (momentScalarAmp2622K02P019Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P019]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P019 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P019 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P019Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P019_replay] at h
  simpa only [momentPanelPhase_owner2622K02P019] using h

theorem momentScalarAmp2622K02P019_radius_le :
    (momentScalarAmp2622K02P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P019Expected]

def momentScalarGrow2622K02P019Input : RatPair2542 := (momentPanelGrowth2622K02P019 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P019Expected : RatState2542 :=
  ((((12579977461561178735310416902861563782814280497796464289265632732783429125693227911595372681084579 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((996686813317694626371376011240990822574754452301 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K02P019_replay :
    compactExp2620 momentScalarGrow2622K02P019Input 20 = momentScalarGrow2622K02P019Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P019_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-141 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P019Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P019Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P019 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P019]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P019 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P019 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P019Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P019Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P019_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P019] using h

theorem momentScalarGrow2622K02P019_radius_le :
    (momentScalarGrow2622K02P019Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P019Expected]

end ConnesWeilRH.Dev
