import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P141 : ℚ := ((-108291539384210056669844853317100468021763051776520211 : ℚ) / 2796549129088057790945605528539340770228353735065600)

def momentPanelGrowth2622K02P141 : ℚ := ((96916329265683062213707001567263057321276152026357 : ℚ) / 154570925120055455118612370491380323270251459379200)

theorem momentPanelPhase_owner2622K02P141 :
    (momentPanelPhase2622K02P141 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (103 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P141, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P141 :
    (momentPanelGrowth2622K02P141 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P141, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P141Input : RatPair2542 := (momentPanelPhase2622K02P141 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P141Expected : RatState2542 :=
  ((((32530759734184724149994336151116956094362569262815103860278884653927199663808909 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10309790607442011509290995613491 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K02P141_replay :
    compactExp2620 momentScalarAmp2622K02P141Input 20 = momentScalarAmp2622K02P141Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P141_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (103 / 200) 0) -
      (momentScalarAmp2622K02P141Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P141]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P141 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P141 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P141Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P141_replay] at h
  simpa only [momentPanelPhase_owner2622K02P141] using h

theorem momentScalarAmp2622K02P141_radius_le :
    (momentScalarAmp2622K02P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P141Expected]

def momentScalarGrow2622K02P141Input : RatPair2542 := (momentPanelGrowth2622K02P141 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P141Expected : RatState2542 :=
  ((((1999273761060093669117497703848258800776428448784704961720739614631114957848694830528616561846747 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2534379067780722401698249475136832538040799830399 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P141_replay :
    compactExp2620 momentScalarGrow2622K02P141Input 20 = momentScalarGrow2622K02P141Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P141_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P141Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P141]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P141 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P141 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P141Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P141_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P141] using h

theorem momentScalarGrow2622K02P141_radius_le :
    (momentScalarGrow2622K02P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P141Expected]

end ConnesWeilRH.Dev
