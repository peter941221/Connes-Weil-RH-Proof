import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P049 : ℚ := ((-358344505497486644153606103158032923100219184344854561 : ℚ) / 9545147119278918492541604906484333573100532871987200)

def momentPanelGrowth2622K02P049 : ℚ := ((1304953572219201995983811862383466432407439361367869573 : ℚ) / 3292458756973670093470272195712502065972225579470028800)

theorem momentPanelPhase_owner2622K02P049 :
    (momentPanelPhase2622K02P049 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P049 :
    (momentPanelGrowth2622K02P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P049Input : RatPair2542 := (momentPanelPhase2622K02P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P049Expected : RatState2542 :=
  ((((52997846881187357655014253442594296968540959069762469798874526518947192683852755 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((67185158999117364739623405904307 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P049_replay :
    compactExp2620 momentScalarAmp2622K02P049Input 20 = momentScalarAmp2622K02P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K02P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P049_replay] at h
  simpa only [momentPanelPhase_owner2622K02P049] using h

theorem momentScalarAmp2622K02P049_radius_le :
    (momentScalarAmp2622K02P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P049Expected]

def momentScalarGrow2622K02P049Input : RatPair2542 := (momentPanelGrowth2622K02P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P049Expected : RatState2542 :=
  ((((3174896611573816673755397678339886917434003166104712048417777651258405845015044442360186993031061 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1006164518515654089256421858884967619240754014699 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P049_replay :
    compactExp2620 momentScalarGrow2622K02P049Input 20 = momentScalarGrow2622K02P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P049] using h

theorem momentScalarGrow2622K02P049_radius_le :
    (momentScalarGrow2622K02P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P049Expected]

end ConnesWeilRH.Dev
